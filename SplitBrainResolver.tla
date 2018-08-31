------------------------- MODULE SplitBrainResolver -------------------------
(*
    There are two or more nodes. Nodes are on a network. They form a cluster. A network split occurs and nodes can not communicate to each other. The cluster gets split in two (or more) parts. Separate parts of would build their own version of the truth if they remain active.

    An algorithm must decide which part to keep active and which to shut down, so that there’s always a single version of the truth. This is a split-brain resolver or SBR.

    A node can be “up” or marked “down” by the SBR.

    This is a specification of an SBR algorithm as an alternative to https://developer.lightbend.com /docs/akka-commercial-addons/current/split-brain-resolver.html
*)

CONSTANT Node               \* The set of nodes on the network

VARIABLE clusterState       \* clusterState[n] is the state of node n from the point of view of the cluster

\* VARIABLE nodePerspective    \* nodePerspective[n] is how a node sees all other nodes on the network

TypeOK == /\ clusterState \in [Node -> {"up", "down"}]
\*          /\ nodePerspective \in [Node -> [Node -> {"up", "unreachable", "down"}]]
        
Init == clusterState = [n \in Node |-> "up"]

GoUp(n) == /\ clusterState[n] = "down"
           /\ clusterState' = [clusterState EXCEPT ![n] = "up"]
           
GoDown(n) == /\ clusterState[n] = "up"
             /\ clusterState' = [clusterState EXCEPT ![n] = "down"]

AllAreUp == \A n \in Node : clusterState[n] = "up"

Next == \E n \in Node : GoUp(n) \/ GoDown(n)

Spec == Init /\ [][Next]_clusterState


=============================================================================
\* Modification History
\* Last modified Fri Aug 31 18:39:44 CEST 2018 by nikola
\* Created Fri Aug 31 13:38:37 CEST 2018 by nikola
