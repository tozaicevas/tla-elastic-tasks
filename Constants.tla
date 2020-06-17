------------------------------- MODULE Constants -------------------------------
EXTENDS TLC, Naturals

_NODES == {0, 1}

_NULL == 9999

_TASK_TO_CANCEL == 0

_INITIAL_TASKS == {
    [
            id |-> 0,
            nodeId |-> 0,
            parentId |-> _NULL,
            status |-> "ACCEPTED"
    ]
}
=============================================================================