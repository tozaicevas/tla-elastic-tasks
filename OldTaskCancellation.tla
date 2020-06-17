------------------------------- MODULE OldTaskCancellation -------------------------------
EXTENDS TLC, Integers, FiniteSets, Naturals, Constants

CONSTANTS NODES,                \* Nodes (represented as integers)
          TASK_TO_CANCEL,       \* Task that needs to be cancelled
          INITIAL_TASKS
        \*   NULL                  \* Needed to represent tasks without parent
        \*   TASKS,                \* Tasks without parents, that are running on Init
        \*   SEARCH_REQUESTS_COUNT,\* Maximum amount of tasks that can be run

VARIABLES bannedTasks, messages, subtasks
\* bannedTasks stores ids


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
    parentId: INITIAL_TASKS \union {NULL},
    status: {"IN_FLIGHT", "DISMISSED", "ACCEPTED"}
]

Message == [
    type: {"BAN", "UNBAN", "CREATE", "CANCEL"},
    task: Task
]

TypeOK == /\ messages \subseteq Message
          /\ bannedTasks \subseteq INITIAL_TASKS
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
        \* /\ taskCounter = Cardinality(INITIAL_TASKS) 
        \* { 0, 1 }
        \* { {task0, task1}, {task0, task1} }

CancelTask ==   /\ \/ Cardinality(messages) = 0
                    \/ \A message \in messages: message /= [type |-> "CANCEL", task |-> TASK_TO_CANCEL]
                /\ bannedTasks' = bannedTasks \union {TASK_TO_CANCEL}
                /\ messages' = messages \union {[type |-> "CANCEL", task |-> TASK_TO_CANCEL]}
                /\ UNCHANGED <<subtasks>>

GetAnyNotBannedTask(node) == (CHOOSE subtask \in subtasks:
                            /\ subtask \notin bannedTasks 
                            /\ subtask.nodeId = node)

ChangeTaskStatus(task, newStatus) == [
    id |-> task.id,
    nodeId |-> task.nodeId,
    parentId |-> task.parentId,
    status |-> newStatus
]

AcceptAnyTask(node) == /\ \E subtask \in subtasks: 
                            /\ subtask.parentId \notin bannedTasks 
                            /\ subtask.nodeId = node
                    /\ subtasks' = (subtasks \ {GetAnyNotBannedTask(node)}) \union {ChangeTaskStatus(GetAnyNotBannedTask(node), "ACCEPTED")}
                    /\ UNCHANGED <<messages, bannedTasks>>

UnbanTask(t) == /\ t.id \in bannedTasks 
                   /\ bannedTasks' = bannedTasks \ {t.id}
                   /\ messages' = messages \union {[type |-> "UNBAN", task |-> t]}
                   /\ UNCHANGED <<subtasks>>

Next == \/ CancelTask
        \/ \E node \in NODES: AcceptAnyTask(node)
        \/ \E task \in INITIAL_TASKS: UnbanTask(task)
        \* \/ 

\* TypeOK == /\ small \in 0..3
\*           /\ big \in 0..5

\* Min(m,n) == IF m < n THEN m ELSE n

\* Init == (small = 0) /\ (big = 0)

\* SmallToBig == (small' = small - Min(small, 5 - big)) /\ (big' = big + Min(small, 5 - big))
\* BigToSmall == (big' = big - Min(big, 3 - small)) /\ (small' = small + Min(big, 3 - small))

\* FillSmall == (big' = big) /\ (small' = 3)
\* FillBig == (small' = small) /\ (big' = 5)

\* EmptySmall == (small' = 0) /\ (big' = big)
\* EmptyBig == (big' = 0) /\ (small' = small)

\* Next == FillSmall \/ FillBig \/ SmallToBig \/ BigToSmall \/ EmptySmall \/ EmptyBig

\* NotSolved == big /= 4

=============================================================================