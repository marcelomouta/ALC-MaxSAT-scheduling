"""
ALC 2nd Project – Single Machine Scheduling with SMT

Group 9:
89513 Nikoletta Matsur
98812 Marcelo Mouta
"""

# from z3 import Optimize, And, Implies
# from z3 import Int
from z3 import *
from itertools import accumulate

import sys
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
            accumulate(reversed(t_frags + [description[DI_INDEX]]), operator.sub)
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

    NOT_STARTING = max_deadline
    num_tasks = len(tasks)
    s = Optimize()

    # intialize variables x, x_i_j -> start time of fragment j from task i
    x = [[] for _ in range(num_tasks)]
    for i in range(num_tasks):
        for j in range(tasks[i][KI_INDEX]):
            name = f"x_{i}_{j}"
            x[i] += [Int(name)]

    # Each task will be represented as: (ri, pi, di, ki, [fragments], [dependencies])
    # Each fragment j of the task i is a tuple: (pij, EST, LST)
    for i in range(num_tasks):

        # CONSTRAINT (1):
        # For each i in {1..n}:
        # x_i_1 >= ri
        # Explanation: make sure that a task starts at or after it's release time
        s.add(x[i][0] >= tasks[i][RI_INDEX])

        ki = tasks[i][KI_INDEX]
        for j in range(ki):

            (pij, est, lst) = tasks[i][FRAGMENTS_INDEX][j]

            # CONSTRAINT (2):
            # x_i_j + pij <= x_i2_j2 || x_i2_j2 + pij2 <= x_i_j
            # Explanation: If a fragment j starts at t, there can't be none starting at the following t'
            for i2 in range(num_tasks):
                if (
                    i2 != i
                    and i2 + 1 not in tasks[i][DEPENDENCIES_INDEX]
                    and i + 1 not in tasks[i2][DEPENDENCIES_INDEX]
                ):

                    ki2 = tasks[i2][KI_INDEX]
                    for j2 in range(ki2):

                        (pij2, est2, lst2) = tasks[i2][FRAGMENTS_INDEX][j2]

                        if est2 < lst + pij and est < lst2 + pij2:
                            # both time intervals intersect: second must start and finish after the second finishes

                            s.add(
                                Or(
                                    x[i][j] + pij <= x[i2][j2],
                                    x[i2][j2] + pij2 <= x[i][j],
                                )
                            )

        # CONSTRAINT (3):
        # For each i in {1..n},  and d in dependencies_i :
        # (X_i,1) >= (X_d,ki' + pki') AND if (X_d,ki' > lst_ki => X_i,1 = NOT_STARTING)
        # Explanation: If a task has a dependency, its' first fragment may only start after the last fragment of the dependency finished
        frag_1 = tasks[i][FRAGMENTS_INDEX][0]
        (_, est, lst) = frag_1

        for d in tasks[i][DEPENDENCIES_INDEX]:
            dep = d - 1
            ki = tasks[dep][KI_INDEX] - 1  # last index of fragments of dependecy d
            frag_ki = tasks[dep][FRAGMENTS_INDEX][ki]
            (pki, est_ki, lst_ki) = frag_ki

            s.add(x[i][0] >= x[dep][ki] + pki)
            s.add(Implies(x[dep][ki] > lst_ki, x[i][0] > NOT_STARTING))
            # if the last fragment from dependency starts after the task's deadline, do not start task

        # CONSTRAINT (4):
        # For each i in {1..n}, and j in {1..ki-1}, and t in {EST_ij+1 .. LST_ij+1} :
        # X_i,j+1 >= X_i,j + pij
        # Explanation: If a fragment j+1 is executed, fragment j is also executed
        for j in range(tasks[i][KI_INDEX] - 1):
            frag_j = tasks[i][FRAGMENTS_INDEX][j]
            frag_j1 = tasks[i][FRAGMENTS_INDEX][j + 1]
            (pij, est, lst) = frag_j

            s.add(x[i][j + 1] >= x[i][j] + pij)

    # SOFT CLAUSES
    # For each i in {1..n} and some j in {1..ki}:
    # x_i_j <= lst
    # Explanation: A fragment of each task starts
    for i in range(num_tasks):
        ki = tasks[i][KI_INDEX] - 1
        (_, _, lst) = tasks[i][FRAGMENTS_INDEX][ki]
        s.add_soft(x[i][ki] <= lst, weight=1)
        s.add(Implies(x[i][ki] > lst, x[i][ki] > max_deadline))

    s.check()
    sol = s.model()
    return sol, x


def produce_output(solution, x, max_deadline):

    num_tasks = len(x)
    executed_tasks = 0

    line = ""
    for i in range(num_tasks):

        last_frag = x[i][-1]  # x_i_j
        if solution[last_frag].as_long() < max_deadline:

            executed_tasks += 1
            line += str(i + 1)
            for x_i_j in x[i]:
                line += " " + str(solution[x_i_j])
            line += "\n"

    line = str(executed_tasks) + "\n" + line
    print(line, end="")


if __name__ == "__main__":

    tasks, max_deadline, accumulated_ki = parse_input()

    solution, x = solve(tasks, max_deadline, accumulated_ki)

    produce_output(solution, x, max_deadline)
