ALC 3rd Project – Single Machine Scheduling with CSP

Group 13:
89513 Nikoletta Matsur
98812 Marcelo Mouta

Consider an input file named job.sms. Run our project as follows:
        ./proj2 < job.sms > solution.txt

If you wish to run minizinc alone you may run like this:
        minizinc model.mzn data.dzn

To solve the Single Machine Scheduling Problem we decided to use the Python
language and the default solver from the minizinc framework.

First we start by modeling the input to a 2D matrix named x, so that a variable 
in the position x[i][j], or simply X_i_j, assigned to 'n' means 
that the fragment j from task i starts in n. 
X is mapped into a 1d array since minizinc only supports 2darrays with fixed 
dimensions but, for simplicity, we'll refer to it as a matrix.

There also are a few more variables that were used throughout the project:

+--------------+-------------------------------------------------------+
| Variable     | Meaning                                               |
|--------------|-------------------------------------------------------+
| est_ij       | Earliest Start Time for the fragment j of the task i  |
| lst_ij       | Latest Start Time for the fragment j of the task i    |
| max_deadline | Latest deadline from all tasks                        |
| E            | E[i] = 1 if task i is executed; E[i] = 0 otherwise.   |
+-------------+--------------------------------------------------------+

NOTE: As there are mixed deadlines, the time that a fragment j from the task i 
could potentially be executed, will correspond the interval {EST_ij .. LST_j}, 
which we refer to as the "possible time".

Then, we proceed to specify the constraints. The problem is being solved
with CSP, and here we present the modeled constraints:

CONSTRAINT (1):
For all i in {1..n}, j in {1..ki}:
        EST_ij <= x_i_j <= LST_ij
Explanation: Each fragment can only be executed during its possible time

CONSTRAINT (2):
For all i, i2 in {1..n}, j in {1..ki}, j2 in {1..ki2}:
        x_i_j + pij <= x_i2_j2 \/ x_i2_j2 + pij2 <= x_i_j
Explanation: There can't be two fragments being executed at the same time

CONSTRAINT (3):
For each i in {1..n}, and d in dependencies_i:
        IF i and d are not mutual deps /\ E[d] = 1: (x_i,1) >= (x_d,kd + pkd) 
        ELSE E[i] = 0 
Explanation: If a task has a dependency, it's first fragment may only start 
after the last fragment of the dependency finished

CONSTRAINT (4):
For each i in {1..n}, and j in {1..ki-1}, and t in {EST_ij+1 .. LST_ij+1} :
        x_i,j+1 >= x_i,j + pij
Explanation: If a fragment j+1 is executed, fragment j is also executed
(finishing before j+1 starts)

CONSTRAINT (5):
        E[i] = 0 -> for all i in {1..n}, and j in {1..ki-1}: x[i,j] = EST_ij
Explanation: If a task is not executed, set its' fragments times to their EST 
NOTE: this constraint further closes the domain, making the solution more 
efficient

Our solution maximizes the number of executed tasks, which is represented as
maximizing the following expression:
        sum(i in 1..n) (E[i])

Given this formulation we consider that these constraints are sufficient to 
produce correct output, that is, to show the maximum number of scheduled tasks.
We also aimed to accurately restrict our clauses so that the efficiency of the 
solution could be improved. 