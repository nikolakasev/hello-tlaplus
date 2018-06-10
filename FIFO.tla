-------------------------------- MODULE FIFO --------------------------------
EXTENDS Naturals, Sequences

CONSTANT Message, N

VARIABLES in, out, q

ASSUME (N \in Nat) /\ (N > 0) \* positive natural number

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

BoundedRcv == /\ (Len(q) < N)
              /\ BufRcv  
          
BufSend == /\ q /= <<>> \* can send to the buffer only if the queue is not empty
           /\ OutChan!Send(out.val)
           /\ q' = Tail(q)
           /\ UNCHANGED in

RRcv == /\ OutChan!Rcv
        /\ UNCHANGED <<in, q>>

Next == \/ (\E m \in Message : SSend(m))
        \/ BoundedRcv
        \/ BufSend
        \/ RRcv

Spec == Init /\ [][Next]_<<in, out, q>>

----

THEOREM Spec => []TypeInvariant

=============================================================================
\* Modification History
\* Last modified Sun Jun 10 16:15:50 CEST 2018 by Nikola
\* Created Sun Jun 10 14:29:18 CEST 2018 by Nikola
