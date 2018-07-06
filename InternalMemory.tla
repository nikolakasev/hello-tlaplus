--------------------------- MODULE InternalMemory ---------------------------
EXTENDS MemoryInterface
VARIABLES mem, ctl, buf

IInit == /\ mem \in [Adr |-> Val]
        /\ ctl = [p \in Proc |-> "ready"] \*each processor is ready to process instructions
        /\ buf = [p \in Proc |-> NoVal] \*each buffer is initialized to NoVal
        /\ memInt \in InitMemInt
        
TypeInvariant == /\ mem \in [Adr -> Val]
                 /\ ctl \in [Proc -> {"ready", "busy", "done"}]
                 /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}] \*remove {} from NoVal? what happens?
                    \*the buffer for a processor can contain the request, the value of the response or no value

Req(p) == /\ ctl[p] = "ready"
          /\ \E req \in MReq:
            /\ Send(p, req, memInt, memInt') \*how is memInt' computed?
            /\ buf' = [buf EXCEPT ![p] = req]
            /\ ctl' = [ctl EXCEPT ![p] = "busy"]
          /\ UNCHANGED mem

Do(p) == /\ ctl[p] = "busy"
         /\ mem' = IF buf[p].op = "Write"
                    THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
                    ELSE mem \*leave the mem unchanged when the request is to read a value
         /\ buf' = [buf EXCEPT
                        ![p] = IF buf[p].op = "Write" 
                                THEN NoVal \* remove the value from the buffer because it was written to memory
                                ELSE mem[buf[p].adr]] \* read and put in the buffer         
         /\ ctl' = [ctl EXCEPT ![p] = "done"]
         /\ UNCHANGED memInt
         
Rsp(p) == /\ ctl[p] = "done"
          /\ Reply(p, buf[p], memInt, memInt')
          /\ ctl' = [ctl EXCEPT ![p] = "ready"]
          /\ UNCHANGED <<mem, buf>>
          
INext == \E p \in Proc: Req(p) \/ Do(p) \/ Rsp(p) \*the next state action

ISpec == IInit /\ [][INext]_<<memInt, mem, ctl, buf>>

-----
THEOREM ISpec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Fri Jul 06 14:09:38 CEST 2018 by nikola
\* Created Mon Jul 02 17:33:48 CEST 2018 by nikola
