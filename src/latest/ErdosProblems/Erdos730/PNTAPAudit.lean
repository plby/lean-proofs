/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.PNTAP

/-!
# Erdős 730 PNT-AP kernel audit

The upstream source contains two admitted declarations in an unrelated
Fourier-decay experiment (`prelim_decay_2` and `prelim_decay_3`).  Neither is
in the transitive dependency cone of `chebyshev_asymptotic_pnt`; the axiom
prints below are the kernel-level check of that fact.
-/

#print axioms chebyshev_asymptotic_pnt
#print axioms WeakPNT_AP
#print axioms Erdos730.FullDensity.primeAPCountingReal_eq_thetaAP_div_log_add_integral
#print axioms Erdos730.FullDensity.primeAPCountingReal_normalized_tendsto
#print axioms Erdos730.FullDensity.pntAPInputAtModulus
#print axioms Erdos730.FullDensity.requiredFixedModulusPNTAPInput
