/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTProfileRescale
import ErdosProblems.Erdos4b.FGKMTMixedTensorSum

/-!
# The literal long-factor tensor sum at the original logarithmic scale

All coordinates range up to `R^2`. The long factor is therefore not
truncated at one. Exact rescaling identifies this sum with the mixed
unit-interval sum to which the uniform mean applies.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem double_log_coordinate (R n : ℕ) :
    2 * (Real.log n / Real.log (R ^ 2 : ℕ)) = Real.log n / Real.log R := by
  rw [log_nat_sq]
  ring

theorem dimensionProfileFactor_log_rescale (k R n : ℕ) :
    dimensionProfileFactor k (Real.log n / Real.log R) =
      sieveFactor (2 * sieveProfileScale k) (sieveProfileWidth k / 2)
        (Real.log n / Real.log (R ^ 2 : ℕ)) := by
  have h := sieveFactor_double_arg (sieveProfileScale k) (sieveProfileWidth k)
    (Real.log n / Real.log (R ^ 2 : ℕ))
  rw [double_log_coordinate] at h
  exact h

theorem dimensionLongFactor_log_rescale (k R n : ℕ) :
    dimensionLongFactor k (Real.log n / Real.log R) =
      sieveFactor (2 * sieveProfileScale k) 1 (Real.log n / Real.log (R ^ 2 : ℕ)) := by
  have h := sieveFactor_double_arg (sieveProfileScale k) 2 (Real.log n / Real.log (R ^ 2 : ℕ))
  rw [double_log_coordinate] at h
  norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0)] at h
  exact h

def longTensorSieveSum (k M : ℕ) (g : ℕ → ℝ) (R j : ℕ) : ℝ :=
  ∑ e : Fin (j + 1) → Fin (R ^ 2 + 1),
    dimensionLongFactor k (Real.log (e 0).val / Real.log R) ^ 2 *
      (∏ i : Fin j, dimensionProfileFactor k (Real.log (e i.succ).val / Real.log R) ^ 2) *
        roughSieveWeight M g (∏ i, (e i).val)

theorem longTensorSieveSum_eq_mixed (k M R j : ℕ) (g : ℕ → ℝ) :
    longTensorSieveSum k M g R j = mixedTensorSieveSum M g (R ^ 2) j
      (fun t => sieveFactor (2 * sieveProfileScale k) 1 t ^ 2)
      (fun t => sieveFactor (2 * sieveProfileScale k) (sieveProfileWidth k / 2) t ^ 2) := by
  unfold longTensorSieveSum mixedTensorSieveSum
  simp_rw [dimensionLongFactor_log_rescale, dimensionProfileFactor_log_rescale]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.longTensorSieveSum_eq_mixed
