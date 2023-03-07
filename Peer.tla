-------------------------------- MODULE Peer --------------------------------

(***************************************************************************)
(* We propose a high-level algorithm, specified in TLA+, for establishing  *)
(* connections between validators in the Stellar network based on the      *)
(* notions of of preferred peers, automatic peers, and random peers.  This *)
(* may not reflect the current implementation.                             *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, TLC

CONSTANTS
    \* the set of validators:
    V, 
    \* the qsets of the validators:
    QSet(_), 
    \* target number of outbound connections (TARGET_PEER_CONNECTIONS in the core config file):
    TargetOutbound,
    \* max number of inbound connections (MAX_ADDITIONAL_PEER_CONNECTIONS in the core config file): 
    MaxInbound,
    \* target number of total connections to qset members (TODO: what's the config variable for this?): 
    MaxAutomatic, \* TODO: name is a bit confusing because preferred also count towards this
     \* set of preferred peers (PREFERRED_PEERS in the core config file):
    Preferred(_)
  

VARIABLES
    connections, \* the set of established connections
    connReqs \* connection requests in flight in the network
    \* NOTE: we do not model pending connections on a validator
    
vars == <<connections, connReqs>>
    
(***************************************************************************)
(* The type invariant:                                                     *)
(***************************************************************************)
TypeOkay ==
    \* A connection is a pair (order matters for the inbound/outbound classification):
    /\ connections \in SUBSET {<<v,w>> : v,w \in V} \* inbound for w, outbound for v
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
NumPreferred(v) == Cardinality(Connected(v) \cap Preferred(v))

(***************************************************************************)
(* the set of validators w in v's qset that v has a connection with:       *)
(***************************************************************************)
\* TODO: again here the name is a bit confusing since it also include preferred peers:
AutomaticConnected(v) == Connected(v) \cap (Preferred(v) \union QSet(v))
NumAutomaticConns(v) == Cardinality(AutomaticConnected(v))
    
(***************************************************************************)
(* v can request a connection to w if v is not connected to w and: v has   *)
(* not reached its target number of outbound connections, or w is in v's   *)
(* qset and v has not reached its target number of automatic connections,  *)
(* or w is a preferred peer.                                               *)
(***************************************************************************)
RequestConnection(v, w) ==
    /\ v # w \* do not connect to self
    /\ w \notin Connected(v) \* v is not connected to w already
    /\ <<v,w>> \notin connReqs \* v hasn't sent a connection request to w already
    /\ \/ NumOutbound(v) < TargetOutbound
       \/ w \in QSet(v) /\ NumAutomaticConns(v) < MaxAutomatic
       \/ w \in Preferred(v)
    /\ connReqs' = connReqs \union {<<v,w>>}
    /\ UNCHANGED connections

(***************************************************************************)
(* The set of validators that have sent a connection request to v:         *)
(***************************************************************************)
PendingReq(v) == {w \in V : <<w,v>> \in connReqs}

(***************************************************************************)
(* v accepts a connection request from w if v has not reached its max      *)
(* number of connections yet, if v has not reached its target number of    *)
(* automatic connections and w is in v's qset, or if w is a preferred      *)
(* peer; in the latter two cases, v might need to disconnect form a        *)
(* non-qset member in order not to exceed its max number of connections.   *)
(***************************************************************************)
AcceptConnection(v, w) ==
    /\  w \in PendingReq(v) \* w has sent a request to v
    /\  w \notin Connected(v) \* v is not already connected to w
    /\ connReqs' = connReqs \ {<<w, v>>} \* connection request received
    /\  IF NumInbound(v) < MaxInbound
        THEN \* we accept the connection
            /\ connections' = connections \union {<<w,v>>} \* we accept the connection
            /\ connReqs' = connReqs \ {<<w, v>>} \* remove the connection request
        ELSE 
            \* v already has MaxConn connections, but maybe it does not have enough qset connections
            \* or it's missing preferred peers
            IF w \in Preferred(v)
            THEN \* three cases: we disconnect a non-qset, non-preferred peer if there is one, 
                 \* or we disconnect a qset peer, or we do not disconnect anyone if we only have preferred peers
                IF ConnectedInbound(v) \ AutomaticConnected(v) # {}
                THEN \E x \in ConnectedInbound(v) \ AutomaticConnected(v) :
                    /\ connections' = (connections \union {<<w,v>>}) \ {<<x, v>>}
                ELSE \* we only have preferred and automatic peers
                    IF ConnectedInbound(v) \ Preferred(v) # {} \* disconnect from a QSet peer
                    THEN \E x \in ConnectedInbound(v) \ Preferred(v) :
                        /\ connections' = (connections \union {<<w,v>>}) \ {<<x,v>>}
                    ELSE \* don't disconnect from anyone (we're only connected to preferred peers
                        /\ connections' = connections \union {<<w,v>>}
            ELSE
                IF w \in QSet(v) /\ NumAutomaticConns(v) < MaxAutomatic
                THEN
                    IF ConnectedInbound(v) \ (Preferred(v) \union AutomaticConnected(v)) # {}
                    THEN \E x \in ConnectedInbound(v) \ (Preferred(v) \union AutomaticConnected(v)) :
                        \* we accept the connection to w but we disconnect from x:
                        /\ connections' = (connections \union {<<w,v>>}) \ {<<x,v>>}
                    ELSE UNCHANGED <<connections>> \* no capacity to connect
                ELSE UNCHANGED <<connections>>
            
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
(* Safety properties                                                       *)
(***************************************************************************)

\* no validator has both an inboud and outbound connection to the same peer:
P1 == \A v,w \in V : \neg {<<v,w>>, <<w,v>>} \subseteq connections
\* no validator has a connection to itself:
P2 == \A v \in V : \neg <<v,v>> \in connections

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
\* Last modified Mon Mar 06 17:19:26 PST 2023 by nano
\* Created Tue Feb 28 16:44:22 PST 2023 by nano
