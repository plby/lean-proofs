import ErdosProblems.Erdos550.Main

/-!
# Public off--Turán route audit

This file deliberately imports only the public theorem root.  The checks below
fix the unconditional signatures and expose every nonconstructive axiom used by
the direct off--Turán theorem and the final Erdős 550 assembly.
-/

#check Erdos550.off_turan_embedding_direct
#check Erdos550.near_turan_red_density_direct
#check Erdos550.erdos_550_large_core
#check Erdos550.erdos_550_large
#check Erdos550.erdos_550

#print axioms Erdos550.off_turan_embedding_direct
#print axioms Erdos550.near_turan_red_density_direct
#print axioms Erdos550.erdos_550_large_core
#print axioms Erdos550.erdos_550_large
#print axioms Erdos550.erdos_550
