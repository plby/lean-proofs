import ErdosProblems.Erdos421.RoughCountInduction

/-! # Unconditional uniform asymptotics for the actual rough-number count -/

namespace Erdos421

def roughCountErrorConstant : ℕ → ℝ
  | 0 => 8
  | n + 1 => 32 * roughCountErrorConstant n * ((n : ℝ) + 3) + 24

theorem roughCountErrorConstant_nonneg (n : ℕ) : 0 ≤ roughCountErrorConstant n := by
  induction n with
  | zero => norm_num [roughCountErrorConstant]
  | succ n ih => dsimp only [roughCountErrorConstant]; positivity

theorem roughCountEstimate_all (n : ℕ) : RoughCountEstimate n (roughCountErrorConstant n) := by
  induction n with
  | zero => exact roughCountEstimate_zero
  | succ n ih => exact roughCountEstimate_step (roughCountErrorConstant_nonneg n) ih

theorem rough_count_asymptotic (n : ℕ) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B > 1, ∀ b : ℝ, B ≤ b → ∀ a : ℝ, b / 2 ≤ a → a ≤ b →
      ∀ z : ℕ, 2 ≤ z → (z : ℝ) ≤ b → b ≤ (z : ℝ) ^ (n + 2) →
      |((roughInRealInterval a b z).card : ℝ) -
        (b - max a z) / Real.log z * finiteBuchstab n (Real.log b / Real.log z)| ≤
        ε * b / (Real.log b) ^ A +
          roughCountErrorConstant n * (b - a) ^ 2 / (b * (Real.log b) ^ 2) :=
  roughCountEstimate_all n A ε hA hε

end Erdos421
