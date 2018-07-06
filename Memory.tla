------------------------------- MODULE Memory -------------------------------
EXTENDS MemoryInterface

Inner(mem, ctl, buf) == INSTANCE InternalMemory
Spec == \E mem, ctl, buf : Inner(mem, ctl, buf) ! ISpec

=============================================================================
\* Modification History
\* Last modified Fri Jul 06 09:20:55 CEST 2018 by nikola
\* Created Fri Jul 06 08:51:56 CEST 2018 by nikola
