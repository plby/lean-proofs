/- Adapted from the checked repository proof in Erdos1148/WeightedPartialSums.lean. -/
import ErdosProblems.Erdos941.DirichletPartialSums
import Mathlib.Algebra.BigOperators.Module

/-! # A quantitative summation-by-parts bound -/

namespace Erdos941.Analytic

theorem norm_sum_range_smul_le_of_antitone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → ℝ) (z : ℕ → E) (hf : Antitone f) (hf₀ : ∀ n, 0 ≤ f n)
    {B : ℝ} (hz : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, f i • z i‖ ≤ B * f 0 := by
  rw [Finset.sum_range_by_parts]
  have hlead : ‖f (n - 1) • ∑ i ∈ Finset.range n, z i‖ ≤ f (n - 1) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf₀ _)]
    exact mul_le_mul_of_nonneg_left (hz n) (hf₀ _)
  have hsum : ‖∑ i ∈ Finset.range (n - 1),
      (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), z j‖ ≤
      ∑ i ∈ Finset.range (n - 1), (f i - f (i + 1)) * B := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hf (Nat.le_succ i))),
      neg_sub]
    exact mul_le_mul_of_nonneg_left (hz _) (sub_nonneg.mpr (hf (Nat.le_succ i)))
  have htel : (∑ i ∈ Finset.range (n - 1), (f i - f (i + 1))) = f 0 - f (n - 1) :=
    Finset.sum_range_sub' f (n - 1)
  calc
    _ ≤ ‖f (n - 1) • ∑ i ∈ Finset.range n, z i‖ +
        ‖∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), z j‖ := norm_sub_le _ _
    _ ≤ f (n - 1) * B + ∑ i ∈ Finset.range (n - 1), (f i - f (i + 1)) * B :=
      add_le_add hlead hsum
    _ = B * f 0 := by rw [← Finset.sum_mul, htel]; ring

end Erdos941.Analytic
