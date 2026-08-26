import ErdosProblems.Erdos1148.RealDirichletValue
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # A logarithmic upper bound at one -/

namespace Erdos1148.DukeArithmetic

theorem realDirichletPartialSum_one_norm_le_harmonic {q : ℕ}
    (χ : DirichletCharacter ℝ q) (n : ℕ) :
    ‖realDirichletPartialSum χ 1 n‖ ≤ (harmonic n : ℝ) := by
  unfold realDirichletPartialSum
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖((k + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) * χ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ))⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Real.rpow_neg_one, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      exact mul_le_of_le_one_right (by positivity) (χ.norm_le_one _)
    _ = (harmonic n : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem realDirichletValue_one_norm_le_log_add_three {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) :
    ‖realDirichletValue χ 1‖ ≤ Real.log q + 3 := by
  have htail := realDirichletValue_sub_partialSum_norm_le χ hχ zero_lt_one q
  have htail' : ‖realDirichletValue χ 1 - realDirichletPartialSum χ 1 q‖ ≤ 2 := by
    apply htail.trans
    rw [Real.rpow_neg_one, ← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((q + 1 : ℕ) : ℝ))).mpr
    push_cast
    linarith
  have hmain := (realDirichletPartialSum_one_norm_le_harmonic χ q).trans (harmonic_le_one_add_log q)
  have hnorm := norm_add_le (realDirichletValue χ 1 - realDirichletPartialSum χ 1 q)
    (realDirichletPartialSum χ 1 q)
  rw [sub_add_cancel] at hnorm
  linarith

end Erdos1148.DukeArithmetic
