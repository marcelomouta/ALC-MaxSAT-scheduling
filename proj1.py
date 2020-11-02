from pysat.examples.rc2 import RC2
from pysat.formula import WCNF
from pysat.card import CardEnc, EncType
from itertools import accumulate

import sys
import fileinput
import operator

RI_INDEX = 0
PI_INDEX = 1
DI_INDEX = 2
KI_INDEX = 3
FRAGMENTS_INDEX = 4
DEPENDENCIES_INDEX = 5
EST_INDEX = 1
LST_INDEX = 2


def parse_input():

    lines = sys.stdin.readlines()
    f_content = [[int(i) for i in l.split()] for l in lines]

    num_tasks = f_content[0][0]

    # description of a task in the form: ri pi di ki j_1 ... j_ki
    task_descriptions = f_content[1 : num_tasks + 1]

    # dependencies of a task in the form: mi t_1 .. t_mi
    dependencies = f_content[num_tasks + 1 : 2 * num_tasks + 1]

    # Each task will be represented as: (ri, pi, di, ki, [fragments], [dependencies])
    tasks = []

    max_deadline = 0

    # list containing the accumulated sum of ki at task i
    ki_sum = 0
    accumulated_ki = [ki_sum]

    for i in range(num_tasks):

        description = task_descriptions[i]

        task_variables = description[:FRAGMENTS_INDEX]
        t_frags = description[FRAGMENTS_INDEX:]

        max_deadline = max(max_deadline, task_variables[DI_INDEX])

        ki_sum += task_variables[KI_INDEX]
        accumulated_ki.append(ki_sum)

        # Each fragment j of the task i is a tuple: (pij, EST, LST)
        # where EST/LST respresents the earliest/latest start time of j
        fragments = []
        current_est = task_variables[RI_INDEX]
        task_lst = list(
            accumulate(reversed(t_frags), operator.sub, initial=description[DI_INDEX])
        )  # 6 [2,1,1] [6-2,6-2-1,6-2-1-1]
        task_lst = task_lst[1:]

        for j in range(task_variables[KI_INDEX]):

            pij = t_frags[j]

            # task_lst is reversed so we must access it backwards with -(j+1)
            frag = (pij, current_est, task_lst[-(j + 1)])
            fragments.append(frag)

            current_est += pij

        task_variables.append(fragments)

        dep = dependencies[i]
        task_variables.append(dep[1:] if dep[0] else [])

        tasks.append(tuple(task_variables))

    return tasks, max_deadline, accumulated_ki


def solve(tasks, max_deadline, accumulated_ki):

    num_tasks = len(tasks)

    # intialize variables x, x_ijt -> fragment j from tasks i is executed and starts at time t
    x = [
        [
            [
                (t + 1) + (j * max_deadline) + (accumulated_ki[i] * max_deadline)
                for t in range(max_deadline)
            ]
            for j in range(tasks[i][KI_INDEX])
        ]
        for i in range(num_tasks)
    ]

    solver = RC2(WCNF())

    # Each task will be represented as: (ri, pi, di, ki, [fragments], [dependencies])
    # Each fragment j of the task i is a tuple: (pij, EST, LST)

    # CONSTRAINT (0)
    # Sum(X_ijt) <= 1  [for i in {i..n}, and j in {1..ki} such that EST_ij <= t <= LST_ij]
    # Explanation: At most, only one fragment starts at each time t:
    for t in range(max_deadline):

        frags_starting_at_t = [
            x[i][j][t]
            for i in range(num_tasks)
            for j in range(tasks[i][KI_INDEX])
            if tasks[i][FRAGMENTS_INDEX][j][EST_INDEX]
            <= t
            <= tasks[i][FRAGMENTS_INDEX][j][LST_INDEX]
        ]

        enc = CardEnc.atmost(
            lits=frags_starting_at_t,
            bound=1,
            top_id=x[-1][-1][-1],
            encoding=EncType.pairwise,
        )
        for clause in enc.clauses:
            solver.add_clause(clause)

    for i in range(num_tasks):

        ki = tasks[i][KI_INDEX]
        for j in range(ki):

            frag_j = tasks[i][FRAGMENTS_INDEX][j]
            (pij, est, lst) = frag_j

            # CONSTRAINT (1)
            # For all i in {1..n},  for all j in {1..ki} :
            # Sum(X_i,j,EST_ij, ... , X_i,j,LST_ij) <= 1
            # Explanation: Each fragment may only be executed at most once
            frag_possible_ts = [x[i][j][t] for t in range(est, lst + 1)]

            enc = CardEnc.atmost(
                lits=frag_possible_ts,
                bound=1,
                top_id=x[-1][-1][-1],
                encoding=EncType.pairwise,
            )
            for clause in enc.clauses:
                solver.add_clause(clause)

            # CONSTRAINT (2):
            # For each i in {1..n}, and j in {1..ki}, and t int {0..EST_ij -1} U {LST_ij +1  .. last_deadline - 1} : ~X_ijt
            # Explanation: Each fragment of a task may only start between its EST and LST
            for t in range(max_deadline):
                if est <= t <= lst:
                    continue
                solver.add_clause([x[i][j][t] * -1])

            # CONSTRAINT (3):
            # X_ijt -> ~X_i'j't'  (with t' in {t+1 .. t+pij-1} and in {EST_ij' .. LST_ij'})
            # Explanation: If a fragment j starts at t, there can't be none starting at the following t'
            for t in range(est, lst + 1):

                for t2 in range(t + 1, t + pij):

                    for i2 in range(num_tasks):
                        ki2 = tasks[i2][KI_INDEX]
                        for j2 in range(ki2):
                            if (i2, j2) != (i, j):

                                (_, est2, lst2) = tasks[i2][FRAGMENTS_INDEX][j2]

                                if est2 <= t2 <= lst2:
                                    solver.add_clause([-x[i][j][t], -x[i2][j2][t2]])

        # CONSTRAINT (4):
        # For each i in {1..n},  and d in dependencies_i, and t in {ESTi1 .. LSTi1} :
        # (X_t,i,1) -> (X_d,ki',ESTki' V .. V X_d,ki',t-pki')
        # Explanation: If a task has a dependency, its' first fragment may only start after the last fragment of the dependency finished
        frag_1 = tasks[i][FRAGMENTS_INDEX][0]
        (_, est, lst) = frag_1

        for d in tasks[i][DEPENDENCIES_INDEX]:
            dep = d - 1
            ki = tasks[dep][KI_INDEX] - 1  # last index of fragments of dependecy d
            frag_ki = tasks[dep][FRAGMENTS_INDEX][ki]
            (pki, est_ki, lst_ki) = frag_ki

            for t in range(est, lst + 1):
                lits = []
                lits.append(x[i][0][t] * -1)

                last = min(t - pki, lst_ki)

                for dki in range(est_ki, last + 1):
                    lits.append(x[dep][ki][dki])

                solver.add_clause(lits)

        # CONSTRAINT (5)
        # (X_i,1,t) -> (X_i,ki,t+pi1 V .. V X_i,ki,LSTki) [with ki > 1, and for all t in {EST_i1 .. LST_i1}]
        # Explanation: If a tasks first fragment is executed, the last one must be as well:
        if ki > 1:
            (pi_1, EST_1, LST_1) = tasks[i][FRAGMENTS_INDEX][0]
            (pi_ki, EST_ki, LST_ki) = tasks[i][FRAGMENTS_INDEX][-1]

            for t in range(EST_1, LST_1 + 1):
                # ki cannot start before frag 1 is finished (t+pi1) or before EST_ki
                ki_min_start_time = max(t + pi_1, EST_ki)

                possible_kis = [
                    x[i][-1][t2] for t2 in range(ki_min_start_time, LST_ki + 1)
                ]
                # ~X_t,i,1  V  X_mint2,i,ki V .. V X_LSTki,i,ki
                const = [-x[i][0][t]] + possible_kis
                solver.add_clause(const)

        # CONSTRAINT (6):
        # For each i in {1..n}, and j in {1..ki-1}, and t in {EST_ij+1 .. LST_ij+1} :
        # X_i,j+1,t -> (X_i,j,ESTij V .. V X_i,j,t-pij)
        # Explanation: If a fragment j+1 is executed, fragment j is also executed
        for j in range(tasks[i][KI_INDEX] - 1):
            frag_j = tasks[i][FRAGMENTS_INDEX][j]
            frag_j1 = tasks[i][FRAGMENTS_INDEX][j + 1]
            (pij, est, lst) = frag_j
            (_, est1, lst1) = frag_j1
            for t in range(est1, lst1 + 1):
                lits = []
                lits.append(x[i][j + 1][t] * -1)

                last = min(t - pij, lst)
                for k in range(est, last + 1):
                    lits.append(x[i][j][k])

                solver.add_clause(lits)

    # SOFT CLAUSES
    # For each i in {1..n} and some j in {1..ki} and t in {ESTij .. LSTij} : Sum(X_ijt) >= 1
    # Explanation: A fragment of each task starts
    for i in range(num_tasks):
        (_, EST_ki, LST_ki) = tasks[i][FRAGMENTS_INDEX][-1]
        lits = [x[i][-1][t] for t in range(EST_ki, LST_ki + 1)]
        solver.add_clause(lits, weight=1)

    sol = solver.compute()
    scheduled_tasks = num_tasks - solver.cost

    return sol, scheduled_tasks


def produce_output(solution, num_scheduled_tasks, accumulated_ki):

    # accumulated_ki = [0,3,5,7,9]
    current_task = 0

    line = str(num_scheduled_tasks)
    for v in solution:
        if v > 0:
            new_task = False

            fragment_number = (v - 1) // max_deadline

            while fragment_number >= accumulated_ki[current_task]:
                current_task += 1
                new_task = True

            if new_task:
                print(line)
                line = str(current_task)

            t = (v - 1) % max_deadline
            line += " " + str(t)

    print(line)


if __name__ == "__main__":

    tasks, max_deadline, accumulated_ki = parse_input()

    solution, scheduled_tasks = solve(tasks, max_deadline, accumulated_ki)

    produce_output(solution, scheduled_tasks, accumulated_ki)
