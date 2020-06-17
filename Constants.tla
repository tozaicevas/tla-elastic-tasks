------------------------------- MODULE Constants -------------------------------
EXTENDS TLC, Naturals

_NODE_IDS == {0, 1}

_NULL == 9999

_PARENT_TASK_TO_CANCEL_ID == 0

_INITIAL_TASKS == {
    [
            id |-> 0,
            nodeId |-> 0,
            parentId |-> _NULL,
            status |-> "ACCEPTED"
    ]
}
=============================================================================