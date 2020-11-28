int: num_tasks;
int: max_deadline;
set of int: accumulated_ki;
array[1..num_tasks] of int: ri;
array[1..num_tasks] of set of int: deps;
array[1..num_frags] of int: est;
array[1..num_frags] of int: lst;
array[1..num_frags] of int: pij;

int: num_frags = accumulated_ki[num_tasks+1];


% array[1..num_tasks] of var set of int: x = [{ "x_\(i)_\(j)" | j in 1..num_frags_task_i(i)} | i in 1..num_tasks];
array[1..num_frags] of var 0..max_deadline: x;

function int: num_frags_task_i(int: i) = accumulated_ki[i+1] - accumulated_ki[i];
function int: frag_ij_index(int: i, int: j) = accumulated_ki[i] + j;
function int: ki_index(int: i) = accumulated_ki[i+1];

predicate frags_intercept(int: i, int: j, int: i2, int: j2) = (est[frag_ij_index(i2,j2)] < lst[frag_ij_index(i,j)] + pij[frag_ij_index(i,j)]) /\ (est[frag_ij_index(i,j)] < lst[frag_ij_index(i2,j2)] + pij[frag_ij_index(i2,j2)]);
% predicate task_is_executed(int: i) = x[ki_index(i)] <= lst[ki_index(i)];
predicate task_is_executed(int: i) = forall(j in 1..num_frags_task_i(i)) (x[frag_ij_index(i,j)] <= lst[frag_ij_index(i,j)]);

% CONSTRAINT (1):
% For each i in {1..n}:
%   x_i_1 >= ri
% Explanation: a task must start at or after it's release time
constraint forall(i in 1..num_tasks) (
    x[frag_ij_index(i,1)] >= ri[i]
);

% CONSTRAINT (2):
% x_i_j + pij <= x_i2_j2 || x_i2_j2 + pij2 <= x_i_j
% Explanation: There can't be two fragments being executed at the same time

constraint forall(i in 1..num_tasks) (
            forall(j in 1..num_frags_task_i(i) where x[frag_ij_index(i,j)] != max_deadline) (
                forall(i2 in 1..num_tasks) (
                    if (i2 != i) /\ (not (i2 in deps[i])) /\ (not (i in deps[i2])) then
                        forall(j2 in 1..num_frags_task_i(i2)  where x[frag_ij_index(i,j)] != max_deadline) (
                            if frags_intercept(i,j,i2,j2) then

                                ((x[frag_ij_index(i,j)] + pij[frag_ij_index(i,j)] )<=  x[frag_ij_index(i2,j2)]) \/ ((x[frag_ij_index(i2,j2)] + pij[frag_ij_index(i2,j2)]) <=  x[frag_ij_index(i,j)])
                            endif
                        )
                    endif
                )
            )
);

    %    for i2 in range(num_tasks):
    %                 if (
    %                     i2 != i
    %                     and i2 + 1 not in tasks[i][DEPENDENCIES_INDEX]
    %                     and i + 1 not in tasks[i2][DEPENDENCIES_INDEX]
    %                 ):

    %                     ki2 = tasks[i2][KI_INDEX]
    %                     for j2 in range(ki2):

    %                         (pij2, est2, lst2) = tasks[i2][FRAGMENTS_INDEX][j2]

    %                         if est2 < lst + pij and est < lst2 + pij2:
    %                             s.add(
    %                                 Or(
    %                                     x[i][j] + pij <= x[i2][j2],
    %                                     x[i2][j2] + pij2 <= x[i][j],
    %                                 )
    %                             )



% CONSTRAINT (3):
% For each i in {1..n},  and d in dependencies_i :
% (x_i,1) >= (x_d,ki' + pki') AND if (x_d,ki' > lst_ki => x_i,1 > NOT_STARTING)
% Explanation: If a task has a dependency, it's first fragment may only start after the last fragment of the dependency finished
constraint forall(i in 1..num_tasks where x[frag_ij_index(i,1)] != max_deadline) (
            forall(d in deps[i]) (
                if not (i in deps[d]) /\  (x[ki_index(d)] <= lst[ki_index(d)]) then
                    (x[frag_ij_index(i,1)] >= x[ki_index(d)] + pij[ki_index(d)])
                else x[frag_ij_index(i,1)] = max_deadline
                endif
            )
);
        % for d in tasks[i][DEPENDENCIES_INDEX]:
        %     dep = d - 1
        %     ki = tasks[dep][KI_INDEX] - 1  # last index of fragments of dependecy d
        %     frag_ki = tasks[dep][FRAGMENTS_INDEX][ki]
        %     (pki, est_ki, lst_ki) = frag_ki

        %     if i + 1 not in tasks[dep][DEPENDENCIES_INDEX]:
        %         s.add(x[i][0] >= x[dep][ki] + pki)
        %         # if the last fragment from dependency starts after the task's deadline, do not start task
        %         s.add(Implies(x[dep][ki] > lst_ki, x[i][0] >= NOT_STARTING))
        %     else:
        %         # task i and d are mutually dependant so i can't be executed
        %         s.add(x[i][0] >= NOT_STARTING)



% CONSTRAINT (4):
% For each i in {1..n}, and j in {1..ki-1}, and t in {EST_ij+1 .. LST_ij+1} :
% x_i,j+1 >= x_i,j + pij
% Explanation: If a fragment j+1 is executed, fragment j is also executed
constraint forall(i in 1..num_tasks) (
            forall(j in 1..(num_frags_task_i(i) - 1)) (
                if x[frag_ij_index(i,j)] != max_deadline then
                    x[frag_ij_index(i,j+1)] >=  x[frag_ij_index(i,j)] + pij[frag_ij_index(i,j)]
                else
                    x[frag_ij_index(i,j+1)] = max_deadline
                endif
            )
);


        %  for j in range(tasks[i][KI_INDEX] - 1):
        %            frag_j = tasks[i][FRAGMENTS_INDEX][j]
        %            frag_j1 = tasks[i][FRAGMENTS_INDEX][j + 1]
        %            (pij, est, lst) = frag_j

        %            s.add(x[i][j + 1] >= x[i][j] + pij)

var int: s = sum(i in 1..num_tasks) (bool2int(task_is_executed(i)));
solve maximize s;

        % for i in range(num_tasks):
        %     ki = tasks[i][KI_INDEX] - 1
        %     (_, _, lst) = tasks[i][FRAGMENTS_INDEX][ki]
        %     s.add_soft(x[i][ki] <= lst, weight=1)

output["\(s)"];

output[if j==1 then "\n" ++ show(i) else "" endif ++  " " ++ show(x[frag_ij_index(i,j)])| i in 1..num_tasks, j in 1..num_frags_task_i(i) where fix(x[accumulated_ki[i+1]]) <= fix(lst[accumulated_ki[i+1]])
];


