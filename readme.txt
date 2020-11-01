ALC 1st Project – Single Machine Scheduling with MaxSAT

Group 9:
89513 Nikoletta Matsur
98812 Marcelo Mouta

To solve the Single Machine Scheduling Problem we decided to use the Python
language and the RC-2 solver from the pysat library.

First we start by modeling the input to a 3D matrix named x, so that a variable 
in the position x[i][j][t], or simply X_ijt, assigned to '1' or 'True' means 
that the fragment j from task i starts in t.

There also are a few more variables that were used throughout the project:

+--------------+-------------------------------------------------------+
| Variable     | Meaning                                               |
|--------------|-------------------------------------------------------+
| EST_ij       | Earliest Start Time for the fragment j of the task i  |
| LST_ij       | Latest Start Time for the fragment j of the task i    |
| max_deadline | Latest deadline from all tasks                        |
+-------------+--------------------------------------------------------+

NOTE: As there are mixed deadlines, the time that a fragment j from the task i 
could potentially be executed, will correspond the interval {EST_ij .. LST_j}, 
which we refer to as the "possible time".

Then, we proceed to specify the constraints. Given that we decided to solve the 
problem with MaxSAT, there will be soft clauses (clauses that can be left 
unsatisfied and the problem still be satisfiable) and hard clauses (clauses 
that must be satisfied). Having this said, we now present the constraint we 
used to get to our hard clauses:

CONSTRAINT (0):
For all i in {i..n}, and j in {1..ki} and EST_ij <= t <= LST_ij:
        Sum(X_ijt) <= 1
Explanation: At most, only one fragment starts at each time t

CONSTRAINT (1):
For all i in {1..n}, and j in {1..ki}, and t in {0..EST_ij - 1} U
{LST_ij + 1  .. max_deadline - 1} :
        ~X_ijt
Explanation: Each fragment of a task may only start between its EST and LST

CONSTRAINT (2):
For all i, i' in {1..n}, j, j' in {1..ki}, t' in {t + 1 .. t + pij -1} and t in 
{EST_ij' .. LST_ij'}:
        X_ijt -> ~X_i'j't' 
Explanation: If a fragment j starts at t, there can't be a fragment j' starting 
at the following t' (while j is still being executed)

CONSTRAINT (3):
For all i in {1..n}, d in dependencies_i, and t in {EST_i1 .. LST_i1} :
    X_i,1,t -> (X_d,ki',ESTki' V .. V X_d,ki',t-pki')
Explanation: If a task i has a dependency d, its' first fragment X_i,1,t may 
only start after the last fragment, ki', of the dependency finished at a time 
in t

CONSTRAINT (4):
With ki > 1, and for all i in {1..n} and t in {EST_i1 .. LST_i1}
    X_i,1,t -> (X_i,ki,t+pi1 V .. V X_i,ki,LSTki)
Explanation: If a tasks first fragment is executed, its' last fragment must also
be executed, in their possible time 

CONSTRAINT (5):
For all i in {1..n}, j in {1..ki-1}, and t in {EST_ij+1 .. LST_ij+1} :
    X_i,j+1,t -> (X_i,j,ESTij V .. V X_i,j,t-pij)
Explanation: If a fragment j+1 is executed, fragment j is also executed, in 
their possible time


Our solution only resorted to one constraint that produces soft clauses, which 
is the following:

CONSTRAINT (6):
For all i in {1..n} and some j in {1..ki} and t in {EST_ij .. LST_ij}:
        Sum(X_ijt) >= 1
Explanation: At least a fragment of each task is executed in its' possible time

Given this formulation we consider that these constraints are sufficient to produce correct output, that is, to show the maximum number of scheduled tasks.
We also aimed to accurately restrict our clauses so that the efficiency of the solution could be improved. 