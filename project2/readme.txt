ALC 2nd Project – Single Machine Scheduling with SMT

Group 9:
89513 Nikoletta Matsur
98812 Marcelo Mouta

Consider an input file named job.sms. Run our project as follows:
        ./proj2 < job.sms > solution.txt

To solve the Single Machine Scheduling Problem we decided to use the Python
language and the Z3 Optimizer from the z3-solver library.

First we start by modeling the input to a 2D matrix named x, so that a variable 
in the position x[i][j], or simply X_i_j, assigned to 'n' means 
that the fragment j from task i starts in n.

There also are a few more variables that were used throughout the project:

+--------------+-------------------------------------------------------+
| Variable     | Meaning                                               |
|--------------|-------------------------------------------------------+
| est_ij       | Earliest Start Time for the fragment j of the task i  |
| lst_ij       | Latest Start Time for the fragment j of the task i    |
| max_deadline | Latest deadline from all tasks                        |
+-------------+--------------------------------------------------------+

NOTE: As there are mixed deadlines, the time that a fragment j from the task i 
could potentially be executed, will correspond the interval {EST_ij .. LST_j}, 
which we refer to as the "possible time".

Then, we proceed to specify the constraints. Given that the problem is solved
with SMT, there are hard clauses (clauses that must be satisfied) but we also
added soft clauses (clauses that can be left unsatisfied and the problem still
be satisfiable) so that the checker doesn't return unsat. Having this said, we
now present the constraint we used to get to our hard clauses:

CONSTRAINT (1):
For each i in {1..n}:
        x_i_1 >= ri
Explanation: a task must start at or after it's release time

CONSTRAINT (2):
        (x_i_j + pij <= x_i2_j2) || (x_i2_j2 + pij2) <= x_i_j
Explanation: Explanation: There can't be two fragments being executed at the
same time

CONSTRAINT (3):
For each i in {1..n},  and d in dependencies_i :
        x_i,1 >= (X_d,ki' + pki') AND 
        if (x_d,ki' > lst_dki) => (x_i,1 > NOT_STARTING)
Explanation: If a task has a dependency, its' first fragment may only start after the last fragment of the dependency finished


CONSTRAINT (4):
For each i in {1..n}, and j in {1..ki-1}, and t in {est_ij+1 .. lst_ij+1} :
        x_i,j+1 >= x_i,j + pij
Explanation: If a fragment j+1 is executed, fragment j is also executed


Our solution only resorted to one constraint that produces soft clauses, which 
is the following:

CONSTRAINT (5):
For all i in {1..n} and some j in {1..ki}:
    x_i_j <= lst_ij
Explanation: The last fragment of each task is executed on its possible time

Given this formulation we consider that these constraints are sufficient to 
produce correct output, that is, to show the maximum number of scheduled tasks.
We also aimed to accurately restrict our clauses so that the efficiency of the 
solution could be improved. 