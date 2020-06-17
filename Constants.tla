------------------------------- MODULE Constants -------------------------------
EXTENDS TLC, Naturals

_NODE_IDS == {0, 1, 2, 3}

_NULL == 9999

_PARENT_TASK_TO_CANCEL_ID == 0

_INITIAL_TASKS == {
    [
            id |-> 0,
            nodeId |-> 3,
            parentId |-> _NULL,
            status |-> "ACCEPTED"
    ],
    [
            id |-> 1,
            nodeId |-> 1,
            parentId |-> _NULL,
            status |-> "ACCEPTED"
    ],
    [
            id |-> 2,
            nodeId |-> 2,
            parentId |-> _NULL,
            status |-> "ACCEPTED"
    ]
}
=============================================================================