/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.OddCofactorLayers
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Erdos822

open scoped BigOperators

theorem harmonic_le_natCast (N : ℕ) : (harmonic N : ℝ) ≤ N := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  calc
    (∑ i ∈ Finset.Icc 1 N, (((i : ℚ)⁻¹ : ℚ) : ℝ)) ≤
        ∑ i ∈ Finset.Icc 1 N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiR : (1 : ℝ) ≤ i := by
        exact_mod_cast (Finset.mem_Icc.mp hi).1
      simp only [Rat.cast_inv, Rat.cast_natCast]
      simpa [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hiR)
    _ = N := by rw [Finset.sum_const]; simp

theorem harmonic_cast_mono {a b : ℕ} (hab : a ≤ b) :
    (harmonic a : ℝ) ≤ (harmonic b : ℝ) := by
  rw [harmonic_eq_sum_Icc, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    rw [Finset.mem_Icc] at hi ⊢
    exact ⟨hi.1, hi.2.trans hab⟩
  · intro i hi hnot
    positivity

theorem sum_inv_oddSmallFactors_le_harmonic (N : ℕ) :
    ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k ≤ (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  calc
    (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) ≤
        ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rw [Finset.mem_Icc]
        exact ⟨oddSmallFactors_pos hk, oddSmallFactors_le hk⟩
      · intro k hk hnot
        positivity
    _ = ∑ k ∈ Finset.Icc 1 N, (((k : ℚ)⁻¹ : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Rat.cast_inv, Rat.cast_natCast]
      ring

/-- The base-two natural logarithm is bounded by twice the real natural
logarithm on positive naturals. -/
theorem natLog_two_le_two_realLog {N : ℕ} (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hraw :
      (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    have h := Real.log2_le_logb N
    simpa [Nat.log2_eq_log_two, Real.logb] using h
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hquot : Real.log (N : ℝ) / Real.log 2 ≤
      2 * Real.log (N : ℝ) := by
    apply (div_le_iff₀ hlog2).2
    nlinarith
  exact hraw.trans hquot

end Erdos822
