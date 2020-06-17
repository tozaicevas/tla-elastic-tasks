------------------------------- MODULE OldTaskCancellation -------------------------------
EXTENDS TLC, Integers, FiniteSets, Naturals, Constants

CONSTANTS NODES,                \* Nodes (represented as integers)
          TASK_TO_CANCEL,       \* Task that needs to be cancelled
          INITIAL_TASKS,
          NULL
        \*   NULL                  \* Needed to represent tasks without parent
        \*   TASKS,                \* Tasks without parents, that are running on Init
        \*   SEARCH_REQUESTS_COUNT,\* Maximum amount of tasks that can be run

VARIABLES bannedTasks, messages, subtasks
\* bannedTasks stores ids
\* subtasks stores full task structures

ASSUME /\ Cardinality(NODES) > 0 
       /\ Cardinality(INITIAL_TASKS) > 0
       /\ NODES \subseteq Nat 
       /\ \E task \in INITIAL_TASKS: task.id = TASK_TO_CANCEL 
       /\ \A task \in INITIAL_TASKS: task.parentId = NULL
       /\ \A task \in INITIAL_TASKS: task.status = "ACCEPTED"
       /\ \A task \in INITIAL_TASKS: \E node \in NODES: node = task.nodeId
       /\ \A taskA, taskB \in INITIAL_TASKS: (taskA /= taskB) => (taskA.id /= taskB.id)

\* INITIAL_TASKS should all be "ACCEPTED"

\* IN_FLIGHT means the task is not yet received
\* DISMISSED means the task is received but not created
\* ACCEPTED means the task is received and created
Task == [
    id: Nat,
    nodeId: NODES,
    parentId: {parentTask.id: parentTask \in INITIAL_TASKS} \union {NULL},
    status: {"IN_FLIGHT", "DISMISSED", "ACCEPTED"}
]

\* rename to parentTaskId
Message == [
    type: {"BAN", "UNBAN", "CREATE"},
    task: Nat
]

TypeOK == /\ messages \subseteq Message
          /\ \A bannedTask \in bannedTasks: \E parentTask \in INITIAL_TASKS: bannedTask = parentTask.id 
          /\ subtasks \subseteq (Task \ INITIAL_TASKS)

GetInitialSubtasks(node) == {[
    id |-> 0, \* id? :/
    nodeId |-> node,
    parentId |-> initialTask.id,
    status |-> "IN_FLIGHT"
]: initialTask \in INITIAL_TASKS} 

Init == /\ bannedTasks = {} 
        /\ messages = {} 
        /\ subtasks = UNION {GetInitialSubtasks(node): node \in NODES}

\* cancels + bans the task
CancelTask ==   /\ \/ Cardinality(messages) = 0
                    \/ \A message \in messages: message /= [type |-> "BAN", task |-> TASK_TO_CANCEL]
                /\ bannedTasks' = bannedTasks \union {TASK_TO_CANCEL}
                /\ messages' = messages \union {[type |-> "BAN", task |-> TASK_TO_CANCEL]}
                /\ UNCHANGED <<subtasks>>

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
AcceptAnyTask(node) == /\ \E subtask \in subtasks: 
                            /\ subtask.parentId \notin bannedTasks 
                            /\ subtask.nodeId = node
                            /\ subtask.status = "IN_FLIGHT"
                    /\ subtasks' = (subtasks \ {GetAnyNotBannedTask(node)}) 
                        \union {ChangeTaskStatus(GetAnyNotBannedTask(node), "ACCEPTED")}
                    /\ UNCHANGED <<messages, bannedTasks>>

DismissSubtask(node) == /\ \E subtask \in subtasks:
                            /\ subtask.parentId \in bannedTasks
                            /\ subtask.nodeId = node
                            /\ subtask.status = "IN_FLIGHT"
                        /\ subtasks' = (subtasks \ {GetAnyBannedTask(node)}) 
                            \union {ChangeTaskStatus(GetAnyBannedTask(node), "DISMISSED")}
                        /\ UNCHANGED <<messages, bannedTasks>>

UnbanTask(t) == /\ t.id \in bannedTasks 
                /\ bannedTasks' = bannedTasks \ {t.id}
                /\ messages' = messages \union {[type |-> "UNBAN", task |-> t.id]}
                /\ UNCHANGED <<subtasks>>

Next == \/ CancelTask
        \/ \E node \in NODES: 
            \/ AcceptAnyTask(node)
            \/ DismissSubtask(node)
        \/ \E task \in INITIAL_TASKS: UnbanTask(task)

AllSubtasksNotAcceptedAfterBan == \A message \in messages:
                                    message.type = "BAN" => ~\E subtask \in subtasks:
                                        /\ subtask.parentId = message.task 
                                        /\ subtask.status = "ACCEPTED"

\* AllSubtasksNotAcceptedAfterBan == \A subtask \in subtasks: 
\*                             (subtask.status = "ACCEPTED") => (\A message \in messages:
\*                                 message /= [type |-> "BAN", task |-> subtask.parentId])

=============================================================================