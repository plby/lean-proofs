import ErdosProblems.Erdos421.DirichletMeanValue
import Mathlib.Algebra.BigOperators.Module

/-! # Summation by parts with monotone nonnegative weights -/

namespace Erdos421

/-- A bound for every prefix persists under multiplication by a decreasing
nonnegative weight, with precisely the initial weight as the factor. -/
theorem norm_sum_antitone_weight_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ℕ → ℝ) (u : ℕ → E) (N : ℕ) (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w)
    {B : ℝ} (hB : 0 ≤ B) (hsum : ∀ n ≤ N, ‖∑ i ∈ Finset.range n, u i‖ ≤ B) :
    ‖∑ i ∈ Finset.range N, w i • u i‖ ≤ w 0 * B := by
  cases N with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, norm_zero] using mul_nonneg (hw 0) hB
  | succ N =>
    rw [Finset.sum_range_by_parts]
    simp only [Nat.succ_sub_one]
    have hlast : ‖w N • ∑ i ∈ Finset.range (N + 1), u i‖ ≤ w N * B := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw N)]
      exact mul_le_mul_of_nonneg_left (hsum (N + 1) le_rfl) (hw N)
    have hparts : ‖∑ i ∈ Finset.range N,
        (w (i + 1) - w i) • ∑ j ∈ Finset.range (i + 1), u j‖ ≤
        ∑ i ∈ Finset.range N, (w i - w (i + 1)) * B := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      have hiN : i + 1 ≤ N + 1 := by have := Finset.mem_range.mp hi; omega
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hanti (Nat.le_succ i)))]
      simpa only [neg_sub] using
        mul_le_mul_of_nonneg_left (hsum (i + 1) hiN) (sub_nonneg.mpr (hanti (Nat.le_succ i)))
    have htel : ∀ L : ℕ, (∑ i ∈ Finset.range L, (w i - w (i + 1))) = w 0 - w L := by
      intro L
      induction L with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih]; ring
    calc
      _ ≤ ‖w N • ∑ i ∈ Finset.range (N + 1), u i‖ +
          ‖∑ i ∈ Finset.range N, (w (i + 1) - w i) •
            ∑ j ∈ Finset.range (i + 1), u j‖ := norm_sub_le _ _
      _ ≤ w N * B + ∑ i ∈ Finset.range N, (w i - w (i + 1)) * B :=
        add_le_add hlast hparts
      _ = _ := by rw [← Finset.sum_mul, htel N]; ring

end Erdos421
