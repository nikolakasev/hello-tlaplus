---- MODULE SplitBrain ----
EXTENDS Naturals, FiniteSets

VARIABLES dc1, dc2
VARIABLE network_split

TypeInvariant == /\ dc1 \in 1..3
                 /\ dc2 \in 4..5
                 /\ network_split = {TRUE, FALSE}

(* Three nodes marked with numbers one to three are live in the first data center and two in the second.
   There is no network split, so nodes in one DC can reach nodes in the other DC. *)
Init == /\ dc1 = {1, 2, 3}
        /\ dc2 = {4, 5}
        /\ network_split = FALSE

Down == /\ Cardinality(dc1 \union dc2) > 0
        /\ dc1' = {}
        /\ dc2' = {}
        /\ UNCHANGED network_split

Next == Down

Spec == Init /\ [][Next]_<<dc1, dc2, network_split>>

THEOREM Spec => []TypeInvariant

(* At least two nodes are live at all times, so that one of them can be updated while the service remains available. *)
AtLeastTwoNodesAreLive == Cardinality(dc1 \union dc2) >= 2
====