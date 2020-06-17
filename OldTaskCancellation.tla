------------------------------- MODULE OldTaskCancellation -------------------------------
EXTENDS TLC, Integers, FiniteSets, Naturals, Constants

CONSTANTS NODES,                \* Nodes (represented as integers)
          TASK_TO_CANCEL,       \* Task that needs to be cancelled
          INITIAL_TASKS,
          NULL

VARIABLES bannedTasks, messages, subtasks, hasSubtaskDecidedAfterBan
\* hasSubtaskDecidedAfterBan is a function from subtask to boolean, indicating whether task 
\* subtask has Accepted/Dismissed request after it was banned at least once
\* bannedTasks is a set currently banned of parent task ids
\* subtasks is a set of all subtasks

ASSUME /\ Cardinality(NODES) > 0 
       /\ Cardinality(INITIAL_TASKS) > 0
       /\ NODES \subseteq Nat 
       /\ \E task \in INITIAL_TASKS: task.id = TASK_TO_CANCEL 
       /\ \A task \in INITIAL_TASKS: task.parentId = NULL
       /\ \A task \in INITIAL_TASKS: task.status = "ACCEPTED"
       /\ \A task \in INITIAL_TASKS: \E node \in NODES: node = task.nodeId
       /\ \A taskA, taskB \in INITIAL_TASKS: (taskA /= taskB) => (taskA.id /= taskB.id)

\* IN_FLIGHT means the create task request is not yet received
\* DISMISSED means the create task request is received but subtask is not created
\* ACCEPTED means the create task request is received and subtask is created
Task == [
    id: Nat,
    nodeId: NODES,
    parentId: {parentTask.id: parentTask \in INITIAL_TASKS} \union {NULL},
    status: {"IN_FLIGHT", "DISMISSED", "ACCEPTED"}
]

\* rename to parentTaskId
Message == [
    type: {"BAN", "UNBAN", "CREATE"},
    taskId: Nat
]

TypeOK == /\ messages \subseteq Message
          /\ \A bannedTask \in bannedTasks: \E parentTask \in INITIAL_TASKS: bannedTask = parentTask.id 
          /\ subtasks \subseteq (Task \ INITIAL_TASKS)
          /\ hasSubtaskDecidedAfterBan \in [{<<task.id, task.nodeId>>: task \in subtasks} -> {FALSE, TRUE}]

\*             rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

\* TCInit == rmState = [rm \in RM |-> "working"]

GetInitialSubtasks(node) == {[
    id |-> 0, 
    nodeId |-> node,
    parentId |-> initialTask.id,
    status |-> "IN_FLIGHT"
]: initialTask \in INITIAL_TASKS} 

Init == /\ bannedTasks = {} 
        /\ messages = {} 
        /\ subtasks = UNION {GetInitialSubtasks(node): node \in NODES}
        /\ hasSubtaskDecidedAfterBan = [x \in {<<task.id, task.nodeId>>: task \in subtasks} |-> FALSE]
        /\ PrintT(hasSubtaskDecidedAfterBan)

\* cancels + bans the task
CancelTask ==   /\ \/ Cardinality(messages) = 0
                    \/ \A message \in messages: message /= [type |-> "BAN", taskId |-> TASK_TO_CANCEL]
                /\ bannedTasks' = bannedTasks \union {TASK_TO_CANCEL}
                /\ messages' = messages \union {[type |-> "BAN", taskId |-> TASK_TO_CANCEL]}
                /\ UNCHANGED <<subtasks, hasSubtaskDecidedAfterBan>>

GetAnyNotBannedTask(node) == (CHOOSE subtask \in subtasks:
                            /\ subtask.parentId \notin bannedTasks 
                            /\ subtask.nodeId = node
                            /\ subtask.status = "IN_FLIGHT")

GetAnyBannedTask(node) == (CHOOSE subtask \in subtasks:
                            /\ subtask.parentId \in bannedTasks 
                            /\ subtask.nodeId = node
                            /\ subtask.status = "IN_FLIGHT")

ChangeTaskStatus(task, newStatus) == [
    id |-> task.id,
    nodeId |-> task.nodeId,
    parentId |-> task.parentId,
    status |-> newStatus
]

\* rename to AcceptAnySubtask
AcceptAnyTask(node) ==  /\ \E subtask \in subtasks: 
                            /\ subtask.parentId \notin bannedTasks 
                            /\ subtask.nodeId = node
                            /\ subtask.status = "IN_FLIGHT"
                        /\ subtasks' = (subtasks \ {GetAnyNotBannedTask(node)}) 
                            \union {ChangeTaskStatus(GetAnyNotBannedTask(node), "ACCEPTED")}
                        /\ hasSubtaskDecidedAfterBan' = 
                            [hasSubtaskDecidedAfterBan EXCEPT ![<<GetAnyNotBannedTask(node).id, node>>] 
                                = \E message \in messages: 
                                    message = [type |-> "BAN", taskId |-> GetAnyNotBannedTask(node).parentId]]
                        /\ UNCHANGED <<messages, bannedTasks>>

DismissSubtask(node) == /\ \E subtask \in subtasks:
                            /\ subtask.parentId \in bannedTasks
                            /\ subtask.nodeId = node
                            /\ subtask.status = "IN_FLIGHT"
                        /\ subtasks' = (subtasks \ {GetAnyBannedTask(node)}) 
                            \union {ChangeTaskStatus(GetAnyBannedTask(node), "DISMISSED")}
                        /\ UNCHANGED <<messages, bannedTasks, hasSubtaskDecidedAfterBan>>

UnbanTask(t) == /\ t.id \in bannedTasks 
                /\ bannedTasks' = bannedTasks \ {t.id}
                /\ messages' = messages \union {[type |-> "UNBAN", taskId |-> t.id]}
                /\ UNCHANGED <<subtasks, hasSubtaskDecidedAfterBan>>

Next == \/ CancelTask
        \/ \E node \in NODES: 
            \/ AcceptAnyTask(node)
            \/ DismissSubtask(node)
        \/ \E task \in INITIAL_TASKS: UnbanTask(task)

SubtasksNotAcceptedAfterBan == \A message \in messages:
                                    message.type = "BAN" => ~\E subtask \in subtasks:
                                        /\ subtask.parentId = message.taskId 
                                        /\ subtask.status = "ACCEPTED"
                                        /\ hasSubtaskDecidedAfterBan[<<subtask.id, subtask.nodeId>>]

=============================================================================