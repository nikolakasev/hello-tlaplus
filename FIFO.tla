-------------------------------- MODULE FIFO --------------------------------
EXTENDS Naturals, Sequences

CONSTANT Message

VARIABLES in, out, q

InChan == INSTANCE Channel WITH Data <- Message, chan <- in
    (* Message substituted for Data and in substituted for chan *)

OutChan == INSTANCE Channel WITH Data <- Message, chan <- out

Init == /\ InChan!Init
        /\ OutChan!Init
        /\ q = <<>>
        
TypeInvariant == /\ InChan!TypeInvariant
                 /\ OutChan!TypeInvariant
                 /\ q \in Seq(Message)

SSend(msg) == /\ InChan!Send(msg)
              /\ UNCHANGED <<q, out>>

BufRcv == /\ InChan!Rcv
          /\ q' = Append(q, in.val)
          /\ UNCHANGED out
          
BufSend == /\ q /= <<>> \* can send to the buffer only if the queue is not empty
           /\ OutChan!Send(out.val)
           /\ q' = Tail(q)
           /\ UNCHANGED in

RRcv == /\ OutChan!Rcv
        /\ UNCHANGED <<in, q>>

Next == \/ (\E m \in Message : SSend(m))
        \/ BufRcv
        \/ BufSend
        \/ RRcv

Spec == Init /\ [][Next]_<<in, out, q>>

----

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Sun Jun 10 15:12:41 CEST 2018 by Nikola
\* Created Sun Jun 10 14:29:18 CEST 2018 by Nikola
