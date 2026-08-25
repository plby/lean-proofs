import ErdosProblems.Erdos67.MRGSA10ExponentialAverage

/-!
# The decaying real-power average in the second A.10 secondary
-/

open MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

theorem intervalIntegral_exp_neg_mul_eq
    {L eta : ℝ} (hL : L ≠ 0) :
    (∫ alpha : ℝ in 0..eta, Real.exp (-L * alpha)) =
      (1 - Real.exp (-L * eta)) / L := by
  have hc := intervalIntegral_cexp_neg_mul_eq (a := L) (eta := eta) hL
  have hc' :
      (∫ alpha : ℝ in 0..eta,
          ((Real.exp (-L * alpha) : ℝ) : ℂ)) =
        (((1 - Real.exp (-L * eta)) / L : ℝ) : ℂ) := by
    simpa using hc
  rw [intervalIntegral.integral_ofReal] at hc'
  exact Complex.ofReal_injective hc'

/-- Exact average of `X^(1-alpha)` on a nonnegative auxiliary interval. -/
theorem intervalIntegral_rpow_one_sub_eq
    {X : ℕ} (hX : 1 < X) (eta : ℝ) :
    (∫ alpha : ℝ in 0..eta, (X : ℝ) ^ (1 - alpha)) =
      (X : ℝ) * (1 - Real.exp (-Real.log X * eta)) /
        Real.log X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlog : Real.log (X : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hX))
  have hfun : (fun alpha : ℝ ↦ (X : ℝ) ^ (1 - alpha)) =
      fun alpha : ℝ ↦ (X : ℝ) *
        Real.exp (-Real.log (X : ℝ) * alpha) := by
    funext alpha
    rw [Real.rpow_def_of_pos hXR,
      show Real.log (X : ℝ) * (1 - alpha) =
        Real.log (X : ℝ) + (-Real.log (X : ℝ) * alpha) by ring,
      Real.exp_add, Real.exp_log hXR]
  rw [hfun, intervalIntegral.integral_const_mul,
    intervalIntegral_exp_neg_mul_eq hlog]
  ring

/-- The source-saving upper bound for the decaying power average. -/
theorem intervalIntegral_rpow_one_sub_le_div_log
    {X : ℕ} (hX : 1 < X) {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta, (X : ℝ) ^ (1 - alpha)) ≤
      (X : ℝ) / Real.log X := by
  have _heta := heta
  rw [intervalIntegral_rpow_one_sub_eq hX eta]
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hexp : 0 ≤ Real.exp (-Real.log (X : ℝ) * eta) :=
    Real.exp_nonneg _
  apply (div_le_div_iff_of_pos_right hlog).2
  have hXR : 0 ≤ (X : ℝ) := Nat.cast_nonneg _
  nlinarith

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.intervalIntegral_rpow_one_sub_eq
#print axioms Erdos67.MRHalaszBands.intervalIntegral_rpow_one_sub_le_div_log
