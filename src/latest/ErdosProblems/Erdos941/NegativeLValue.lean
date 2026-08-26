import ErdosProblems.Erdos941.NegativeQuadraticCharacter
import ErdosProblems.Erdos941.SiegelLowerBound

/-! # A uniform lower bound for the negative quadratic L-values -/

namespace Erdos941

theorem exists_negative_LValue_lower {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) [NeZero n],
      c * (n : ℝ) ^ (-δ) ≤ (DirichletCharacter.LFunction (negativeQuadraticCharacter n) 1).re := by
  obtain ⟨C, hC, hbound⟩ := Analytic.exists_quadratic_LFunction_one_re_lower hδ
  refine ⟨C * (4 : ℝ) ^ (-δ), mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro n hn
  have h := hbound (4 * n) (negativeQuadraticCharacter n)
    (negativeQuadraticCharacter_ne_one n) (negativeQuadraticCharacter_isQuadratic n)
  rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4)
    (Nat.cast_nonneg n)] at h
  simpa only [mul_assoc] using h

end Erdos941
