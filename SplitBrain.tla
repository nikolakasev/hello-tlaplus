(* This is a model of two data centers (DC) and nodes running in them and they form an Akka cluster.
   Let's assume that a node can detect that it can't reach any other node from the other DC.
   The question we are asking is: What are the steps in a runbook that guarantee the integity of knowledge across the cluster?
   Or more specifically: Can we let the second DC shut itself down when a network split occurs and later bring it back up manually? *)
---- MODULE SplitBrain ----
EXTENDS Naturals, FiniteSets

VARIABLES dc1, dc2
VARIABLE network_split

TypeInvariant == /\ dc1 \in 1..3
                 /\ dc2 \in 4..5
                 /\ network_split = {TRUE, FALSE}

(* Three nodes marked with numbers one to three are live in the first data center and two in the second.
   There is no network split, so nodes in one DC can reach nodes in the other DC.
   The nodes in the DC2 are on the minority side of the cluster because they are one less than DC1. *)
Init == /\ dc1 = {1, 2, 3}
        /\ dc2 = {4, 5}
        /\ network_split = FALSE

(* There is no connectivity between the two data centers. *)
NetworkSplitOccurs == /\ network_split = FALSE
                      /\ network_split' = TRUE
                      /\ UNCHANGED <<dc1, dc2>>

(* Assume that a node can detect that it can't reach any of the nodes from the other DC. *)
ShutDownAutomatically == /\ network_split = TRUE
            /\ dc2' = {}
            /\ UNCHANGED <<dc1, network_split>>

(* Somehow the network comes back up. *)
NetworkIsBack == /\ network_split = TRUE
                 /\ network_split' = FALSE
                 /\ UNCHANGED <<dc1, dc2>>

(* Here's the manual part of the runbook, bring the second DC back up. *)
BringDC2Manually == /\ dc2 = {}
                    /\ network_split = FALSE
                    /\ dc2' = {4, 5}
                    /\ UNCHANGED <<dc1, network_split>>

Next == \/ NetworkSplitOccurs
        \/ ShutDownAutomatically
        \/ NetworkIsBack
        \/ BringDC2Manually

Spec == Init /\ [][Next]_<<dc1, dc2, network_split>>

THEOREM Spec => []TypeInvariant

(* At least two nodes are live at all times, so that one of them can be updated while the service remains available. *)
AtLeastTwoNodesAreLive == Cardinality(dc1 \union dc2) >= 2
====