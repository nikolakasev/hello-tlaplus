------------------------- MODULE WriteThroughCache -------------------------
EXTENDS Naturals, Sequences, MemoryInterface
VARIABLES wmem, ctl, buf, cache, memQ
CONSTANT QLen \* the queue depth
ASSUME (QLen \in Nat) /\ (QLen > 0)
M == INSTANCE InternalMemory WITH mem <- wmem

----
Init ==
    /\ M!IInit
    /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
    /\ memQ = <<>> \* the queue is empty
    
TypeInvariant ==
    /\ wmem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"ready", "busy", "waiting", "done"}]
    /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
    /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
    /\ memQ \in Seq(Proc \times MReq) \* all possible <processor, request> pairs?
    
Coherence == \A p, q \in Proc, a \in Adr:
    (NoVal /= {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])
    
----

Req(p) == M!Req(p) /\ UNCHANGED <<cache, memQ>>

Rsp(p) == M!Rsp(p) /\ UNCHANGED <<cache, memQ>>

RdMiss(p) ==
    /\ (ctl[p] = "busy") /\ (buf[p].op = "Read")
    /\ cache[p][buf[p].adr] = NoVal
    /\ Len(memQ) < QLen
    /\ memQ' = Append(memQ, <<p, buf[p]>>)
    /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
    /\ UNCHANGED <<memInt, wmem, buf, cache>> \*what is the purpose of memInt here?
    
=============================================================================
\* Modification History
\* Last modified Fri Jul 06 14:34:10 CEST 2018 by nikola
\* Created Fri Jul 06 10:48:18 CEST 2018 by nikola
