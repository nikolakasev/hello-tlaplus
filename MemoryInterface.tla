-------------------------- MODULE MemoryInterface --------------------------

VARIABLE memInt
CONSTANTS Send(_, _, _, _), \* processor p sending value d to the memory
          Reply(_, _, _, _), \* the memory sending value d to the processor
          InitMemInt, \* The set of possible initial values of memInt
          Proc, \* The set of processor identifiers
          Adr, \* The set of memory addresses
          Val \* the set of memory values
          
ASSUME \A p, d, miOld, miNew : /\ Send(p, d, miOld, miNew) \in BOOLEAN
                               /\ Reply(p, d, miOld, miNew) \in BOOLEAN
                               
MReq == [op: {"Read"}, adr: Adr] \cup [op: {"Write"}, adr: Adr, val: Val]
        \*The set of all requests: read an address, write a value to an address
        
NoVal == CHOOSE v : v \notin Val \*An arbitrary value not in Val
=============================================================================
\* Modification History
\* Last modified Mon Jul 02 17:30:58 CEST 2018 by nikola
\* Created Mon Jul 02 17:19:48 CEST 2018 by nikola
