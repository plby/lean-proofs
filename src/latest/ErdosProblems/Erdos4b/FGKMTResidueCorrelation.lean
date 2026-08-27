/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTResidueProductBound
import Mathlib.Analysis.Complex.Exponential

/-! # From the logarithmic product bound to a relative probability error -/

namespace Erdos4b.FGKMT

noncomputable section

theorem residueAvoidance_ratio_error {S : Finset ℕ} {N : Finset ℤ} {w : ℕ} {H : ℝ}
    (hw : 0 < w) (hS : ∀ p ∈ S, p.Prime) (hrough : ∀ p ∈ S, w < p)
    (ht : 1 ≤ N.card) (hsize : 2 * N.card ≤ w)
    (hH : 1 ≤ H) (hN : ∀ n ∈ N, |(n : ℝ)| ≤ H)
    (hsmall : residueCorrelationError w N.card H ≤ 1) :
    |residueAvoidanceMass S N / residueSieveDensity S ^ N.card - 1| ≤
      2 * residueCorrelationError w N.card H := by
  have hlog := residueAvoidance_log_ratio_bound hw hS hrough ht hsize hH hN
  have hApos := residueAvoidanceMass_pos (N := N) (fun p hp => (hS p hp).pos)
    (fun p hp => by have := hrough p hp; omega)
  have hspos := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  have hratio := div_pos hApos (pow_pos hspos N.card)
  have hexp := Real.abs_exp_sub_one_le (hlog.trans hsmall)
  rw [Real.exp_log hratio] at hexp
  exact hexp.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

theorem residueCorrelationError_le_logSaving {A L : ℝ} {w t : ℕ}
    (hA : 0 ≤ A) (hL : 1 ≤ L) (hw : L ^ 20 / 2 ≤ (w : ℝ))
    (ht : (t : ℝ) ≤ L) {H : ℝ} (hH : 1 ≤ H)
    (hlogH : Real.log (2 * H) ≤ (A + 1) * L) :
    residueCorrelationError w t H ≤ 24 * (A + 1) / L ^ 16 := by
  have hLpos : 0 < L := by linarith
  have hwpos : (0 : ℝ) < w := (by positivity : 0 < L ^ 20 / 2).trans_le hw
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hlog0 : 0 ≤ Real.log (2 * H) := Real.log_nonneg (by linarith)
  have hpow2 := pow_le_pow_left₀ ht0 ht 2
  have hpow3 := pow_le_pow_left₀ ht0 ht 3
  have hL24 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL (by norm_num)
  have hL4 : 0 ≤ L ^ 4 := by positivity
  have hpart : (t : ℝ) ^ 3 * Real.log (2 * H) ≤ L ^ 3 * ((A + 1) * L) :=
    mul_le_mul hpow3 hlogH hlog0 (by positivity)
  have hnum : 8 * (t : ℝ) ^ 2 + 4 * (t : ℝ) ^ 3 * Real.log (2 * H) ≤
      12 * (A + 1) * L ^ 4 := by
    nlinarith [mul_nonneg hA hL4]
  unfold residueCorrelationError
  calc
    _ ≤ 12 * (A + 1) * L ^ 4 / w := div_le_div_of_nonneg_right hnum hwpos.le
    _ ≤ 12 * (A + 1) * L ^ 4 / (L ^ 20 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hw
    _ = _ := by field_simp; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.residueAvoidance_ratio_error
#print axioms Erdos4b.FGKMT.residueCorrelationError_le_logSaving
