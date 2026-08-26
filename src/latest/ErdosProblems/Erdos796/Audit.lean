import ErdosProblems.Erdos796.FullProof

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
This file records the kernel dependencies of the public release theorems.
Run it with `lake env lean --trust=0 Audit.lean`.
-/

#print axioms Erdos796.finite_cutoff_100_lt
#print axioms Erdos796.finite_cutoff_100_combined_lt
#print axioms Erdos796.mertensM_lt_933_div_1000
#print axioms Erdos796.MertensM_lt_one
#print axioms Erdos796.secondOrderConstant_lt_fifteen
#print axioms Erdos796.hasSecondOrderConstant
#print axioms Erdos796.erdosProblem796
