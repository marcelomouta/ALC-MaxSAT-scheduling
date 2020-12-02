import sys
import operator
import subprocess

from itertools import accumulate

RI_INDEX = 0
PI_INDEX = 1
DI_INDEX = 2
KI_INDEX = 3
FRAGMENTS_INDEX = 4
DEPENDENCIES_INDEX = 5


def parse_input():

    lines = sys.stdin.readlines()
    f_content = [[int(i) for i in l.split()] for l in lines]

    num_tasks = f_content[0][0]

    # description of a task in the form: ri pi di ki j_1 ... j_ki
    task_descriptions = f_content[1 : num_tasks + 1]

    # dependencies of a task in the form: mi t_1 .. t_mi
    dependencies = f_content[num_tasks + 1 : 2 * num_tasks + 1]

    ri = []
    pij = []
    est = []
    lst = []
    deps = "["

    max_deadline = 0

    # list containing the accumulated sum of ki at task i
    ki_sum = 0
    accumulated_ki = [ki_sum]

    for i in range(num_tasks):

        description = task_descriptions[i]

        task_variables = description[:FRAGMENTS_INDEX]
        t_frags = description[FRAGMENTS_INDEX:]

        ri.append(task_variables[RI_INDEX])
        max_deadline = max(max_deadline, task_variables[DI_INDEX])

        ki_sum += task_variables[KI_INDEX]
        accumulated_ki.append(ki_sum)

        # Each fragment j of the task i is a tuple: (pij, EST, LST)
        # where EST/LST respresents the earliest/latest start time of j
        current_est = task_variables[RI_INDEX]
        task_lst = list(
            accumulate(reversed(t_frags + [description[DI_INDEX]]), operator.sub)
        )  # 6 [2,1,1] [6-2,6-2-1,6-2-1-1]
        task_lst = task_lst[1:]

        for j in range(task_variables[KI_INDEX]):

            frag_pij = t_frags[j]

            pij.append(frag_pij)
            est.append(current_est)
            # task_lst is reversed so we must access it backwards with -(j+1)
            lst.append(task_lst[-(j + 1)])

            current_est += frag_pij

        dep = dependencies[i]
        deps += "{" + str(dep[1:])[1:-1] + "}," if dep[0] else "{},"
    deps = deps[:-1] + "]"
    return num_tasks, max_deadline, accumulated_ki, ri, est, lst, pij, deps


def format_data(num_tasks, max_deadline, accumulated_ki, ri, est, lst, pij, deps):
    return (
        "num_tasks = {};\n".format(num_tasks)
        + "max_deadline = {};\n".format(max_deadline)
        + "accumulated_ki = { "
        + str(accumulated_ki)[1:-1]
        + " };\n"
        + "ri = {};\n".format(ri)
        + "pij = {};\n".format(pij)
        + "est = {};\n".format(est)
        + "lst = {};\n".format(lst)
        + "deps = {};".format(deps)
    )


if __name__ == "__main__":

    num_tasks, max_deadline, accumulated_ki, ri, est, lst, pij, deps = parse_input()

    data = format_data(num_tasks, max_deadline, accumulated_ki, ri, est, lst, pij, deps)

    ps = subprocess.Popen(
        ("minizinc", "--search-complete-msg", "", "--soln-sep", "", "model.mzn", "-"),
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        encoding="utf-8",
    )
    output, _ = ps.communicate(data)
    output = output[:-1]
    print(output)