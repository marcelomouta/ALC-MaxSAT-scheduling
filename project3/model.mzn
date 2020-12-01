include "alldifferent_except_0.mzn";

int: num_tasks;
int: max_deadline;
set of int: accumulated_ki;
array[1..num_tasks] of int: ri;
array[1..num_tasks] of set of int: deps;
array[1..num_frags] of int: est;
array[1..num_frags] of int: lst;
array[1..num_frags] of int: pij;

int: num_frags = accumulated_ki[num_tasks+1];

array[1..num_frags] of var 0..(max_deadline-1): x;
array[1..num_tasks] of var 0..1: E;

function int: num_frags_task_i(int: i) = accumulated_ki[i+1] - accumulated_ki[i];
function int: frag_ij_index(int: i, int: j) = accumulated_ki[i] + j;
function int: ki_index(int: i) = accumulated_ki[i+1];

predicate frags_intercept(int: i, int: j, int: i2, int: j2) = (est[frag_ij_index(i2,j2)] < lst[frag_ij_index(i,j)] + pij[frag_ij_index(i,j)]) /\ (est[frag_ij_index(i,j)] < lst[frag_ij_index(i2,j2)] + pij[frag_ij_index(i2,j2)]);

% CONSTRAINT (1):
% For each i in {1..n}:
%   x_i_1 >= ri
% Explanation: a task must start at or after it's release time
constraint forall(i in 1..num_tasks) (
            forall(j in 1..num_frags_task_i(i)) (
                x[frag_ij_index(i,j)] >= est[frag_ij_index(i,j)] /\ x[frag_ij_index(i,j)] <= lst[frag_ij_index(i,j)] 
            ) \/ E[i] = 0
);  

% CONSTRAINT (2):
% x_i_j + pij <= x_i2_j2 || x_i2_j2 + pij2 <= x_i_j
% Explanation: There can't be two fragments being executed at the same time
constraint forall(i in 1..num_tasks) (
            forall(j in 1..num_frags_task_i(i)) (
                forall(i2 in 1..num_tasks) (
                    if (i2 != i) /\ (not (i2 in deps[i])) /\ (not (i in deps[i2])) then
                        forall(j2 in 1..num_frags_task_i(i2)) (
                            if frags_intercept(i,j,i2,j2) /\ E[i] + E[i2] = 2 then
                                ((x[frag_ij_index(i,j)] + pij[frag_ij_index(i,j)] )<=  x[frag_ij_index(i2,j2)]) \/ ((x[frag_ij_index(i2,j2)] + pij[frag_ij_index(i2,j2)]) <=  x[frag_ij_index(i,j)])
                            endif
                        )
                    endif
                )
            )
);

% CONSTRAINT (3):
% For each i in {1..n},  and d in dependencies_i :
% (x_i,1) >= (x_d,ki' + pki') AND if (x_d,ki' > lst_ki => x_i,1 > NOT_STARTING)
% Explanation: If a task has a dependency, it's first fragment may only start after the last fragment of the dependency finished
constraint forall(i in 1..num_tasks) (
            forall(d in deps[i]) (
                if not (i in deps[d]) /\ E[d] = 1 then
                    (x[frag_ij_index(i,1)] >= x[ki_index(d)] + pij[ki_index(d)]) \/ E[i] = 0
                else 
                    E[i] = 0
                endif
            )
);

% CONSTRAINT (4):
% For each i in {1..n}, and j in {1..ki-1}, and t in {EST_ij+1 .. LST_ij+1} :
% x_i,j+1 >= x_i,j + pij
% Explanation: If a fragment j+1 is executed, fragment j is also executed
constraint forall(i in 1..num_tasks) (
            forall(j in 1..(num_frags_task_i(i) - 1)) (
                x[frag_ij_index(i,j+1)] >=  x[frag_ij_index(i,j)] + pij[frag_ij_index(i,j)]
            ) \/ E[i] = 0
);

var 1..num_tasks: s = sum(i in 1..num_tasks) (E[i]);
solve %::int_search([s], largest, indomain_split) 
    maximize s;

output["\(s)"];

output[if j==1 then "\n" ++ show(i) else "" endif ++  " " ++ show(x[frag_ij_index(i,j)])| i in 1..num_tasks, j in 1..num_frags_task_i(i) where fix(E[i]) = 1
];


