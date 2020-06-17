------------------------------- MODULE OldTaskCancellation -------------------------------
EXTENDS TLC, Integers, FiniteSets, Naturals, Constants

CONSTANTS NODE_IDS,                \* Nodes (represented as integers)
          TASK_TO_CANCEL,       \* Task that needs to be cancelled
          INITIAL_TASKS,
          NULL

VARIABLES bannedTasks, messages, subtasks, hasSubtaskDecidedAfterBan
\* hasSubtaskDecidedAfterBan is a function from subtask to boolean, indicating whether task 
\* subtask has Accepted/Dismissed request after it was banned at least once
\* bannedTasks is a set currently banned of parent task ids
\* subtasks is a set of all subtasks

ASSUME /\ Cardinality(NODE_IDS) > 0 
       /\ Cardinality(INITIAL_TASKS) > 0
       /\ NODE_IDS \subseteq Nat 
       /\ \E task \in INITIAL_TASKS: task.id = TASK_TO_CANCEL 
       /\ \A task \in INITIAL_TASKS: task.parentId = NULL
       /\ \A task \in INITIAL_TASKS: task.status = "ACCEPTED"
       /\ \A task \in INITIAL_TASKS: \E node \in NODE_IDS: node = task.nodeId
       /\ \A taskA, taskB \in INITIAL_TASKS: (taskA /= taskB) => (taskA.id /= taskB.id)

\* IN_FLIGHT means the create task request is not yet received
\* DISMISSED means the create task request is received but subtask is not created
\* ACCEPTED means the create task request is received and subtask is created
Task == [
    id: Nat,
    nodeId: NODE_IDS,
    parentId: {parentTask.id: parentTask \in INITIAL_TASKS} \union {NULL},
    status: {"IN_FLIGHT", "DISMISSED", "ACCEPTED"}
]

\* rename to parentTaskId
Message == [
    type: {"BAN", "UNBAN", "CREATE"},
    parentTaskId: Nat
]

TypeOK == /\ messages \subseteq Message
          /\ \A bannedTask \in bannedTasks: \E parentTask \in INITIAL_TASKS: bannedTask = parentTask.id 
          /\ subtasks \subseteq (Task \ INITIAL_TASKS)
          /\ hasSubtaskDecidedAfterBan \in [{<<task.id, task.nodeId>>: task \in subtasks} -> {FALSE, TRUE}]

GetInitialSubtasks(node) == {[
    id |-> 0, 
    nodeId |-> node,
    parentId |-> initialTask.id,
    status |-> "IN_FLIGHT"
]: initialTask \in INITIAL_TASKS} 

Init == /\ bannedTasks = {} 
        /\ messages = {} 
        /\ subtasks = UNION {GetInitialSubtasks(node): node \in NODE_IDS}
        /\ hasSubtaskDecidedAfterBan = [x \in {<<task.id, task.nodeId>>: task \in subtasks} |-> FALSE]
        /\ PrintT(hasSubtaskDecidedAfterBan)

\* cancels + bans the task
CancelTask ==   /\ \/ Cardinality(messages) = 0
                    \/ \A message \in messages: message /= [type |-> "BAN", parentTaskId |-> TASK_TO_CANCEL]
                /\ bannedTasks' = bannedTasks \union {TASK_TO_CANCEL}
                /\ messages' = messages \union {[type |-> "BAN", parentTaskId |-> TASK_TO_CANCEL]}
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
                                    message = [type |-> "BAN", parentTaskId |-> GetAnyNotBannedTask(node).parentId]]
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
                /\ messages' = messages \union {[type |-> "UNBAN", parentTaskId |-> t.id]}
                /\ UNCHANGED <<subtasks, hasSubtaskDecidedAfterBan>>

Next == \/ CancelTask
        \/ \E node \in NODE_IDS: 
            \/ AcceptAnyTask(node)
            \/ DismissSubtask(node)
        \/ \E task \in INITIAL_TASKS: UnbanTask(task)

SubtasksNotAcceptedAfterBan == \A message \in messages:
                                    message.type = "BAN" => ~\E subtask \in subtasks:
                                        /\ subtask.parentId = message.parentTaskId 
                                        /\ subtask.status = "ACCEPTED"
                                        /\ hasSubtaskDecidedAfterBan[<<subtask.id, subtask.nodeId>>]

=============================================================================