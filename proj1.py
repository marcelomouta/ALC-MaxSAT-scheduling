from pysat.examples.rc2 import RC2
from pysat.formula import WCNF
from pysat.card import CardEnc
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
PIJ_INDEX = 0
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
    # Each fragment has a corresponding earliest/lates starting time, represented as a tuple: (EST,LST)
    frag_start_time = []

    max_deadline = 0

    # list containing the accumulated sum of ki at task i
    accumulated_ki = []
    ki_sum = 0

    for i in range(num_tasks):

        accumulated_ki.append(ki_sum)

        description = task_descriptions[i]

        task_variables = description[:FRAGMENTS_INDEX]
        t_frags = description[FRAGMENTS_INDEX:]

        max_deadline = max(max_deadline, task_variables[DI_INDEX])

        # Each fragment j of the task i is a tuple: (pij, EST, LST)
        fragments = []
        current_est = task_variables[RI_INDEX]
        task_lst = list(
            accumulate(reversed(t_frags), operator.sub, initial=description[DI_INDEX])
        )  # 6 [2,1,1] [6-2,6-2-1,6-2-1-1]
        task_lst = task_lst[1:]

        for j in range(task_variables[KI_INDEX]):

            pij = t_frags[j]

            # task_lst is reversed so we must access it backwards with -(i+1)
            frag = (pij, current_est, task_lst[-(j + 1)])
            fragments.append(frag)

            current_est += pij

        task_variables.append(fragments)

        dep = dependencies[i]
        task_variables.append(dep[1:] if dep[0] else [])

        tasks.append(tuple(task_variables))

        ki_sum += task_variables[KI_INDEX]

    return tasks, max_deadline, accumulated_ki


def solve(tasks, max_deadline, accumulated_ki):

    num_tasks = len(tasks)

    # intialize variables x, xijt -> fragment j from tasks i is executed and starts at time t
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
    print(x)

    solver = RC2(WCNF())
    max_var = x[-1][-1][-1]  # the last element

    # Each task will be represented as: (ri, pi, di, ki, [fragments], [dependencies])
    # Each fragment j of the task i is a tuple: (pij, EST, LST)

    # Constraint 1
    # For each i in {1..n}, and j in {1..ki}, and t int {0..EST_j -1} U {LST_j +1  .. last_deadline - 1} : ~X_tij
    # Explanation: Each fragment of a task may only start between its EST and LST

    print("CONSTRAINT 1")
    for i in range(num_tasks):
        for j in range(tasks[i][KI_INDEX]):
            frag_j = tasks[i][FRAGMENTS_INDEX][j]
            (_, est, lst) = frag_j
            for t in range(max_deadline):
                if est <= t <= lst:
                    continue
                # solver.add(x[i][j][t] * -1)
                print(x[i][j][t] * -1)

    # Constraint 3
    # For each i in {1..n},  and d in dependencies_i, and t in {ESTi1 .. LSTi1} :
    # (X_t,i,1) -> (X_ESTki',d,ki' V .. V X_t-pki',d,ki')
    # Explanation: If a task has a dependency, its' first fragment may only start after the last fragment of the dependency finished
    print("CONSTRAINT 3")
    for i in range(num_tasks):
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

                print(lits)
                # solver.add(lits)

    # Constraint 5
    # For each i in {1..n}, and j in {1..ki-1}, and t in {EST_ij .. LST_ij} :
    # X_t,i,j+1 -> (X_ESTij,i,j V .. V X_t-pij,i,j)
    # Explanation: If a fragment j+1 is executed, fragment j is also executed
    print("CONSTRAINT 5")
    for i in range(num_tasks):
        for j in range(tasks[i][KI_INDEX] - 1):
            frag_j = tasks[i][FRAGMENTS_INDEX][j]
            (pij, est, lst) = frag_j
            for t in range(est + 1, lst + 1):
                lits = []
                lits.append(x[i][j + 1][t] * -1)

                for k in range(est, t - pij + 1):
                    lits.append(x[i][j][k])

                print(lits)
                # solver.add(lits)

    # IN HERE IS JUST A MAXSAT EXAMPLE CODE

    # initialize variables: vij -> vertex i is colored with j
    # v = [[(i+1) + j * N for j in range(k)] for i in range(N)]

    # solver = RC2(WCNF())
    # max_var = 10  # the problem has 10 variables

    # # HARD CLAUSES
    # constraint = CardEnc.atmost(lits=[1, 2, 3, 4, 5], bound=1, top_id=max_var)
    # for clause in constraint.clauses:
    #     solver.add_clause(clause)
    #     max_var = max(clause + [max_var])

    # constraint = CardEnc.atleast(lits=[4, 5, 6, 7, 8], bound=3, top_id=max_var)
    # for clause in constraint.clauses:
    #     solver.add_clause(clause)
    #     max_var = max(clause + [max_var])

    # # SOFT CLAUSES
    # for i, j in zip(range(10), range(1, 11)):
    #     solver.add_clause([i, j], weight=1)

    # print("Model", solver.compute())
    # print("Cost:", solver.cost)


def produce_output(solution):

    for x in solution:
        print(x)


if __name__ == "__main__":

    tasks, max_deadline, accumulated_ki = parse_input()

    solve(tasks, max_deadline, accumulated_ki)

    produce_output(tasks)
