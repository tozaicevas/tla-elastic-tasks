------------------------------- MODULE Constants -------------------------------
EXTENDS TLC

CONSTANTS NULL

TASKS == {
    [
            id |-> 0,
            nodeId |-> 0,
            parentId |-> NULL,
            status |-> "ACCEPTED"
    ]
}
=============================================================================