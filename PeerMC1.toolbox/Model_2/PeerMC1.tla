------------------------------ MODULE PeerMC1 ------------------------------

CONSTANTS v1,v2,v3,v4

V == {v1,v2,v3,v4}
QSet(v) == CASE
    v = v1 -> {v2,v3}
[]  v = v2 -> {v3,v4}
[]  v = v3 -> {v4,v1}
[]  v = v4 -> {v1,v2}

MaxConn == 1
QSetConn == 0

VARIABLES connections, connReqs

INSTANCE Peer


=============================================================================
\* Modification History
\* Last modified Tue Feb 28 18:14:45 PST 2023 by nano
\* Created Tue Feb 28 17:50:29 PST 2023 by nano
