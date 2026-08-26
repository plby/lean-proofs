import ErdosProblems.Erdos796.BaselineAsymptotic
import PrimeNumberTheoremAnd.Consequences

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The prime-number-theorem input

This module transports the prime-counting asymptotic proved in the
`PrimeNumberTheoremAnd` library from a real variable to the natural-variable
normalization used by this project.
-/

namespace Erdos796

open Filter Topology Asymptotics

/-- The prime number theorem in the exact normalization used by the baseline
and cofactor-model arguments. -/
theorem primeNumberTheorem : PrimeNumberTheorem := by
  have hEqReal := pi_alt'
  have hEqNat :
      (fun n : ℕ => (Nat.primeCounting n : ℝ)) ~[atTop]
        (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
    convert! hEqReal.comp_tendsto tendsto_natCast_atTop_atTop using 1
    ext n
    simp
  have hdenom : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hlog0 : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
    exact div_ne_zero hn0 hlog0
  have hratio := (isEquivalent_iff_tendsto_one hdenom).mp hEqNat
  simpa [PrimeNumberTheorem, secondOrderScale] using! hratio

end Erdos796
