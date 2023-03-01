------------------------------ MODULE PeerMC1 ------------------------------

CONSTANTS v1,v2,v3,v4

V == {v1,v2,v3,v4}
QSet(v) == CASE
    v = v1 -> {v2,v3}
[]  v = v2 -> {v3,v4}
[]  v = v3 -> {v4,v1}
[]  v = v4 -> {v1,v2}

MaxConn == 3
QSetConn == 1

VARIABLES connections, connReqs

INSTANCE Peer

=============================================================================
\* Modification History
\* Last modified Wed Mar 01 07:57:30 PST 2023 by nano
\* Created Tue Feb 28 17:50:29 PST 2023 by nano
