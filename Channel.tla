------------------------------ MODULE Channel ------------------------------
EXTENDS Naturals
CONSTANT Data
VARIABLE chan

TypeInvariant == chan \in [val: Data, rdy: {0,1}, ack: {0,1}]

Init == /\ TypeInvariant
        /\ chan.ack = chan.rdy
        
Send(d) == /\ chan.rdy = chan.ack
           /\ chan' = [chan EXCEPT !.val = d, !.rdy = 1 - @]
           
Rcv == /\ chan.rdy # chan.ack
       /\ chan' = [chan EXCEPT !.ack = 1 - @]
       
Next == (\E d \in Data : Send(d)) \/ Rcv

Spec == Init /\ [][Next]_<<chan>>

----

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Sun Jun 10 14:39:15 CEST 2018 by Nikola
\* Created Sun Jun 10 14:33:10 CEST 2018 by Nikola
