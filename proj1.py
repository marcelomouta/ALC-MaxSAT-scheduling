from pysat.examples.rc2 import RC2
from pysat.formula import WCNF
from pysat.card import CardEnc
from itertools import accumulate

import sys
import fileinput
import operator

def parse_input():

    lines = sys.stdin.readlines()
    f_content = [[int(i) for i in l.split()] for l in lines]
    
    num_tasks = f_content[0][0]

    # description of a task in the form: ri pi di ki j_1 ... j_ki
    task_descriptions = f_content[1:num_tasks+1]

    # dependencies of a task in the form: mi t_1 .. t_mi
    dependencies = f_content[num_tasks+1:2*num_tasks+1]

    # Each task will be represented as: (ri, pi, di, ki, [fragments], [dependencies]) 
    tasks = []
    # Each fragment has a corresponding earliest/lates starting time, represented as a tuple: (EST,LST)
    frag_start_time = []
    
    for i in range(num_tasks):
        
        description = task_descriptions[i]
        t = description[:5]
        t.append(description[5:])

        dep = dependencies[i]
        t.append(dep[1:] if dep[0] else [])

        tasks.append(tuple(t))


    return tasks

def solve(tasks):
    
    # IN HERE IS JUST A MAXSAT EXAMPLE CODE

    # initialize variables: vij -> vertex i is colored with j
    #v = [[(i+1) + j * N for j in range(k)] for i in range(N)]

    solver = RC2(WCNF())
    max_var = 10 # the problem has 10 variables

    # HARD CLAUSES
    constraint = CardEnc.atmost(lits=[1,2,3,4,5], bound=1, top_id=max_var)
    for clause in constraint.clauses:
        solver.add_clause(clause)
        max_var = max(clause + [max_var])

    constraint = CardEnc.atleast(lits=[4,5,6,7,8], bound=3, top_id=max_var)
    for clause in constraint.clauses:
        solver.add_clause(clause)
        max_var = max(clause + [max_var])

    # SOFT CLAUSES
    for i, j in zip(range(10), range(1,11)):
        solver.add_clause([i, j], weight=1)

    print("Model", solver.compute())
    print("Cost:", solver.cost)



def produce_output(solution):
    
    for x in solution:
        print(x)

if __name__ == "__main__":

    tasks = parse_input()

    #solve(tasks)
    
    produce_output(tasks)