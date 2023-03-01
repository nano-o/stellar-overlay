-------------------------------- MODULE Peer --------------------------------

(***************************************************************************)
(* We specify in TLA+ the process of establishing connections between      *)
(* validators in the Stellar network.  This does not reflect the current   *)
(* implementation.                                                         *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, TLC

CONSTANTS
    V, \* the validators
    QSet(_), \* the qsets of the validators
    TargetOutbound, \* target number of outbound connections
    MaxInbound, \* max number of inbound connections
    TargetQSet \* target number of total connections to qset members

VARIABLES
    connections, \* the set of established connections
    connReqs \* connection requests
    
vars == <<connections, connReqs>>
    
(***************************************************************************)
(* The type invariant:                                                     *)
(***************************************************************************)
TypeOkay ==
    \* A connection is a pair (order matters for the inbound/outbound classification):
    /\ connections \in SUBSET {<<v,w>> : v,w \in V}
    /\ connReqs \in SUBSET {<<v,w>> : v,w \in V} \* request from v1 to connect with v2

(***************************************************************************)
(* The initial state:                                                      *)
(***************************************************************************)    
Init ==
    /\ connections = {}
    /\ connReqs = {}

(***************************************************************************)
(* the set of validators w that v has a connection with:                   *)
(***************************************************************************)
Connected(v) == {w \in V : <<v,w>> \in connections \/ <<w,v>> \in connections}

(***************************************************************************)
(* Inbound and outbound connections of v:                                  *)
(***************************************************************************)
ConnectedInbound(v) == {w \in V : <<w,v>> \in connections}
NumInbound(v) == Cardinality(ConnectedInbound(v))
ConnectedOutbound(v) == {w \in V : <<v,w>> \in connections}
NumOutbound(v) == Cardinality(ConnectedOutbound(v))

(***************************************************************************)
(* the set of validators w in v's qset that v has a connection with:       *)
(***************************************************************************)
QSetConnected(v) == Connected(v) \cap QSet(v)
NumQSetConns(v) == Cardinality(QSetConnected(v))
    
(***************************************************************************)
(* v can request a connection to w as long as v has not reached its target *)
(* number of outbound connections or, if w is in v's qset, as long as v    *)
(* has not reached its target number of qset connections.                  *)
(***************************************************************************)
RequestConnection(v, w) ==
    /\ v # w \* do not connect to self
    /\ w \notin Connected(v) \* v is not connected to w already
    /\ <<v,w>> \notin connReqs \* v hasn't sent a connection request to w already
    /\ \/ NumOutbound(v) < TargetOutbound
       \/ w \in QSet(v) /\ NumQSetConns(v) < TargetQSet
       \* Note that with this rule we might exceed our target number of outbound connections
    /\ connReqs' = connReqs \union {<<v,w>>}
    /\ UNCHANGED connections

(***************************************************************************)
(* The set of validators that have sent a connection request to v:         *)
(***************************************************************************)
PendingReq(v) == {w \in V : <<w,v>> \in connReqs}

ConnectionTo(v, w) ==
    IF w \in Connected(v)
    THEN
        IF <<v,w>> \in connections
        THEN <<v,w>>
        ELSE <<w,v>>
    ELSE <<>>

(***************************************************************************)
(* v accepts a connection request from w if v has not reached its max      *)
(* number of connections yet or if v has not reached its target number of  *)
(* qset connections and w is in v's qset; in the latter case, v might need *)
(* to disconnect form a non-qset member in order not to exceed its max     *)
(* number of connections.                                                  *)
(***************************************************************************)
AcceptConnection(v, w) ==
    /\  w \in PendingReq(v) \* w has sent a request to v
    /\  w \notin Connected(v) \* v is not already connected to w
    /\  IF NumInbound(v) < MaxInbound
        THEN \* we accept the connection
            /\ connections' = connections \union {<<w,v>>} \* we accept the connection
            /\ connReqs' = connReqs \ {<<w, v>>} \* remove the connection request
        ELSE \* v already has MaxConn connections, but maybe it does not have enough qset connections
            IF w \in QSet(v) /\ NumQSetConns(v) < TargetQSet
            THEN \E x \in Connected(v) \ QSetConnected(v) : \* TODO: prefer removing inbound or outbound?
                \* we accept the connection to w but we disconnect from x:
                /\ connections' = (connections \union {<<w,v>>}) \ {ConnectionTo(v, x)}
                /\ connReqs' = connReqs \ {<<w, v>>} \* remove the connection request
            ELSE UNCHANGED <<connections, connReqs>>
            
(***************************************************************************)
(* The next-state relation:                                                *)
(***************************************************************************)
Next == \E v,w \in V :
    \/ RequestConnection(v,w)
    \/ AcceptConnection(v, w)
    
(***************************************************************************)
(* The full behavioral specification:                                      *)
(***************************************************************************)
Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ \A v,w \in V : 
        /\ WF_vars(RequestConnection(v,w))
        /\ WF_vars(AcceptConnection(v,w))

(***************************************************************************)
(* Now we make some definitions to check whether a graph is connected      *)
(***************************************************************************)

\* Breadth-first traversal, accumulating vertices in acc:
RECURSIVE TraverseRec(_, _) 
TraverseRec(graph, acc) == 
    LET newVs == {w \in V \ acc : 
            \E v \in acc : <<v,w>> \in graph \/ <<w,v>> \in graph}
    IN IF newVs # {}
        THEN TraverseRec(graph, acc \union newVs)
        ELSE acc  
        
(***************************************************************************)
(* A graph is connected iff, starting from any vertice, the traversal      *)
(* reaches all vertices:                                                   *)
(***************************************************************************)
IsConnectedGraph(graph) ==
    TraverseRec(graph, {CHOOSE v \in V : TRUE}) = V

(***************************************************************************)
(* Eventually, we must obtain a connected graph:                           *)
(***************************************************************************)
Liveness == <>(IsConnectedGraph(connections))

=============================================================================
\* Modification History
\* Last modified Wed Mar 01 12:16:06 PST 2023 by nano
\* Created Tue Feb 28 16:44:22 PST 2023 by nano
