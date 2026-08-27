/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTResidueLogBounds

/-! # Quantitative exponential approximation to a finite avoidance product -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {I : Type*} [Fintype I]

def finiteMissProduct (h : I → ℝ) : ℝ := ∏ i, (1 - h i)

theorem finiteMissProduct_pos {h : I → ℝ} (hh : ∀ i, h i ≤ 1 / 2) :
    0 < finiteMissProduct h := Finset.prod_pos fun i _hi => by linarith [hh i]

theorem finiteMissProduct_le_one {h : I → ℝ} (h0 : ∀ i, 0 ≤ h i) (hh : ∀ i, h i ≤ 1 / 2) :
    finiteMissProduct h ≤ 1 :=
  Finset.prod_le_one (fun i _hi => by linarith [hh i]) (fun i _hi => by linarith [h0 i])

theorem finiteMissProduct_log_error {h : I → ℝ}
    (h0 : ∀ i, 0 ≤ h i) (hh : ∀ i, h i ≤ 1 / 2) :
    |Real.log (finiteMissProduct h) + ∑ i, h i| ≤ 2 * ∑ i, h i ^ 2 := by
  have hn (i : I) : 1 - h i ≠ 0 := ne_of_gt (by linarith [hh i])
  rw [finiteMissProduct, Real.log_prod (fun i _hi => hn i), ← Finset.sum_add_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _hi => log_one_sub_remainder_bound (h0 i) (hh i))

theorem finiteMissProduct_log_target_error {h : I → ℝ} {T ε : ℝ}
    (h0 : ∀ i, 0 ≤ h i) (hh : ∀ i, h i ≤ 1 / 2)
    (hmean : |(∑ i, h i) - T| ≤ ε) :
    |Real.log (finiteMissProduct h / Real.exp (-T))| ≤ 2 * (∑ i, h i ^ 2) + ε := by
  rw [Real.log_div (finiteMissProduct_pos hh).ne' (Real.exp_pos _).ne', Real.log_exp]
  have heq : Real.log (finiteMissProduct h) - -T =
      (Real.log (finiteMissProduct h) + ∑ i, h i) - ((∑ i, h i) - T) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add (finiteMissProduct_log_error h0 hh) hmean)

theorem finiteMissProduct_relative_target_error {h : I → ℝ} {T ε : ℝ}
    (h0 : ∀ i, 0 ≤ h i) (hh : ∀ i, h i ≤ 1 / 2)
    (hmean : |(∑ i, h i) - T| ≤ ε) (hsmall : 2 * (∑ i, h i ^ 2) + ε ≤ 1) :
    |finiteMissProduct h / Real.exp (-T) - 1| ≤ 2 * (2 * (∑ i, h i ^ 2) + ε) := by
  have hlog := finiteMissProduct_log_target_error h0 hh hmean
  have hexp := Real.abs_exp_sub_one_le (hlog.trans hsmall)
  rw [Real.exp_log (div_pos (finiteMissProduct_pos hh) (Real.exp_pos _))] at hexp
  exact hexp.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

theorem finiteMissProduct_target_error {h : I → ℝ} {T ε : ℝ}
    (h0 : ∀ i, 0 ≤ h i) (hh : ∀ i, h i ≤ 1 / 2) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hmean : |(∑ i, h i) - T| ≤ ε) (hsmall : 2 * (∑ i, h i ^ 2) + ε ≤ 1) :
    |finiteMissProduct h - Real.exp (-T)| ≤ 2 * (2 * (∑ i, h i ^ 2) + ε) := by
  have hrel := finiteMissProduct_relative_target_error h0 hh hmean hsmall
  have hpos := Real.exp_pos (-T)
  have hle : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hid : finiteMissProduct h - Real.exp (-T) =
      Real.exp (-T) * (finiteMissProduct h / Real.exp (-T) - 1) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hpos]
  calc
    _ ≤ Real.exp (-T) * (2 * (2 * (∑ i, h i ^ 2) + ε)) :=
      mul_le_mul_of_nonneg_left hrel hpos.le
    _ ≤ 1 * (2 * (2 * (∑ i, h i ^ 2) + ε)) :=
      mul_le_mul_of_nonneg_right hle (by positivity)
    _ = _ := one_mul _

end

end Erdos4b.FGKMT
