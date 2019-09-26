------------------------- MODULE SplitBrainResolver -------------------------
(*
    There are two or more nodes. Nodes are on a network. They form a cluster. A network split occurs and nodes can not communicate to each other. The cluster gets split in two (or more) parts. Separate parts of would build their own version of the truth if they remain active.

    An algorithm must decide which part to keep active and which to shut down, so that there’s always a single version of the truth. This is a split-brain resolver or SBR.

    A node can be “up” or marked “down” by the SBR.

    This is a specification of an SBR algorithm as an alternative to https://developer.lightbend.com /docs/akka-commercial-addons/current/split-brain-resolver.html
*)

CONSTANT Node           \* The set of nodes on the network

VARIABLE actualState    \* actualState[n] is the state of a node

VARIABLE nodeView       \* nodeView[n] is how a node sees all other nodes on the network

TypeInvariant == /\ actualState \in [Node -> {"up", "down"}]
                 /\ nodeView \in [Node -> [Node -> {"up", "unreachable", "down"}]]
        
Init == /\ actualState = [n \in Node |-> "up"]                   \* the cluster sees all nodes are up
        /\ nodeView = [n \in Node |-> [other \in Node |-> "up"]] \* a healthy cluster, all nodes have the same view of the truth
           
GoDown(node) == /\ actualState[node] = "up"
                /\ actualState' = [actualState EXCEPT ![node] = "down"]
                /\ UNCHANGED nodeView \* TODO this isn't correct
             
BecomeUnreachable(node, another) == /\ actualState[node] = "up" \* a node that's down is already marked as such and unreachble is irrelevant
                                    /\ nodeView[another][node] = "up"
                                    /\ nodeView' = [nodeView EXCEPT ![another][node] = "unreachable"]
                                    /\ UNCHANGED actualState
                           
BecomeReachable(node, another) == /\ nodeView[another][node] = "unreachable" \* the network is repaired or the node is responding OK
                                  /\ nodeView' = [nodeView EXCEPT ![another][node] = "up"]
                                  /\ UNCHANGED actualState
                                    
\*TODO
MarkAnotherAsDown(node, another) == TRUE

IsHealthyAccordingTo(node) == \A other \in Node : nodeView[node][other] = "up"

AllAreUp == \A n \in Node : actualState[n] = "up"

AtLeastOneIsUp == \E n \in Node : actualState[n] = "up"

Next == \/ \E n \in Node : GoDown(n)
        \/ \E m, n \in Node: m /= n /\ (BecomeUnreachable(m, n) \/ BecomeReachable(m, n)) \*is m /= n necessary?

Spec == Init /\ [][Next]_<<actualState, nodeView>>


=============================================================================
\* Modification History
\* Last modified Thu Sep 26 17:43:37 CEST 2019 by nikola
\* Created Fri Aug 31 13:38:37 CEST 2018 by nikola
