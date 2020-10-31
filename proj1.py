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

    for i in range(num_tasks):

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

        for i in range(task_variables[KI_INDEX]):

            pij = t_frags[i]

            # task_lst is reversed so we must access it backwards with -(i+1)
            frag = (pij, current_est, task_lst[-(i + 1)])
            fragments.append(frag)

            current_est += pij

        task_variables.append(fragments)

        dep = dependencies[i]
        task_variables.append(dep[1:] if dep[0] else [])

        tasks.append(tuple(task_variables))

    return tasks, max_deadline


def solve(tasks, max_deadline):

    num_tasks = len(tasks)

    # just to test
    tasks_ki = [t[KI_INDEX] for t in tasks[:-1]]
    accumulated_ki = list(accumulate(tasks_ki, initial=0))
    print(accumulated_ki)

    # intialize variables x, xijt -> fragment j from tasks i is executed and starts at time t
    x = [
        [
            [
                (t + 1)
                + (j * (max_deadline - 1))
                + (accumulated_ki[i] * (max_deadline - 1))
                for t in range(max_deadline - 1)
            ]
            for j in range(tasks[i][KI_INDEX])
        ]
        for i in range(num_tasks)
    ]

    print(x)

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

    tasks, max_deadline = parse_input()

    solve(tasks, max_deadline)

    produce_output(tasks)