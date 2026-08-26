/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Low- and high-coefficient truncation estimates on a dyadic spatial interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.DyadicIntervals
import ErdosProblems.Erdos521.WindowError
import ErdosProblems.Erdos521.DyadicWindows

namespace Erdos521

theorem dyadic_bin_distance {k : ℕ} {x : ℝ} (hx : x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1))) :
    1 / (2 : ℝ) ^ (k + 1) ≤ 1 - x ∧ 1 - x ≤ 1 / (2 : ℝ) ^ k := by
  obtain ⟨hl, hu⟩ := hx
  unfold dyadicPoint at hl hu
  constructor <;> linarith

theorem dyadic_window_low_bound {k q : ℕ} (hqk : q ≤ k) {x : ℝ}
    (hx : x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1))) :
    (2 : ℝ) ^ (k - q) * (1 - x) ≤ ((2 : ℝ) ^ q)⁻¹ := by
  calc
    _ ≤ (2 : ℝ) ^ (k - q) * (1 / (2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_left (dyadic_bin_distance hx).2 (by positivity)
    _ = _ := by
      have heq : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - q) * (2 : ℝ) ^ q := by
        rw [← pow_add, Nat.sub_add_cancel hqk]
      rw [heq]
      field_simp

theorem dyadic_window_high_exponent {k q : ℕ} {x : ℝ}
    (hx : x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1))) :
    (2 : ℝ) ^ q ≤ 2 * ((2 : ℝ) ^ (k + q) + 1) * (1 - x) := by
  calc
    (2 : ℝ) ^ q = (2 * (2 : ℝ) ^ (k + q)) / (2 : ℝ) ^ (k + 1) := by
      rw [pow_add, pow_succ]
      field_simp
    _ ≤ (2 * ((2 : ℝ) ^ (k + q) + 1)) / (2 : ℝ) ^ (k + 1) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 2 * ((2 : ℝ) ^ (k + q) + 1) * (1 / (2 : ℝ) ^ (k + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (dyadic_bin_distance hx).1 (by positivity)

theorem exp_neg_le_inv_of_pos {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ y⁻¹ := by
  rw [Real.exp_neg]
  apply (inv_le_inv₀ (Real.exp_pos y) hy).mpr
  linarith [Real.add_one_le_exp y]

theorem dyadic_window_high_bound {k q : ℕ} {x : ℝ} (hx₀ : 0 ≤ x)
    (hx : x ∈ Set.Icc (dyadicPoint k) (dyadicPoint (k + 1))) :
    x ^ (2 * (2 ^ (k + q) + 1)) ≤ ((2 : ℝ) ^ q)⁻¹ := by
  have h := pow_le_exp_nat_mul (u := -(1 - x)) hx₀ (by linarith : x ≤ 1 + -(1 - x))
    (2 * (2 ^ (k + q) + 1))
  apply h.trans
  apply le_trans _ (exp_neg_le_inv_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) q))
  apply Real.exp_le_exp.mpr
  have hbound := dyadic_window_high_exponent (q := q) hx
  push_cast
  nlinarith

theorem dyadicCoefficientWindow_eq_Ico {n k q : ℕ} (hH : 2 ^ (k + q) ≤ n) :
    dyadicCoefficientWindow n k q = Finset.Ico (2 ^ (k - q)) (2 ^ (k + q) + 1) := by
  rw [dyadicCoefficientWindow, min_eq_right hH, Finset.Ico_add_one_right_eq_Icc]

end Erdos521
