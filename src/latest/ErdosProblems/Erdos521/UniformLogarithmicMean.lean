/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform local root expectations on admissible bulk intervals.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LogarithmicMean
import ErdosProblems.Erdos521.UniformLimitCriterion
import ErdosProblems.Erdos521.BulkDegreeRatio

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem normalized_logGrid_one (s ℓ : ℝ) : logGrid s (Real.exp ℓ) ℓ 1 = 1 - 1 / s := by
  rw [logGrid_one, Real.exp_neg, mul_inv_cancel₀ (Real.exp_ne_zero _)]

theorem uniform_logarithmic_mean :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℝ, 0 < ℓ → ∀ η : ℝ, 0 < η →
      ∃ M : ℕ, 2 ≤ M ∧ ∀ n : ℕ, M ≤ n → ∀ s : ℝ, (M : ℝ) ≤ s →
        1 - 1 / s ≤ endpointCenter C n →
        |(∫ ε, (intervalRootCount ε n (1 - Real.exp ℓ / s) (1 - 1 / s) : ℝ) ∂sequenceLaw) -
          ℓ / (2 * Real.pi)| < η := by
  obtain ⟨C, hC, hmean⟩ := logarithmic_mean_limit
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ
  apply uniform_limit_of_admissible_sequences
  intro n s hn hs hbulk
  have hb : ∀ᶠ j : ℕ in atTop, 1 - 1 / s j ≤ endpointCenter C (n j) := Eventually.of_forall hbulk
  have hdegree := bulk_degree_ratio_tendsto n s hC hn hs hb
  have h := hmean n s hn hs hdegree (Real.exp ℓ) ℓ (Real.exp_pos _) hℓ (by
    simpa only [normalized_logGrid_one] using hb)
  simpa only [normalized_logGrid_one, logGrid_zero] using h

theorem uniform_polynomial_zero_probability :
    ∀ η : ℝ, 0 < η → ∃ M : ℕ, 2 ≤ M ∧ ∀ n : ℕ, M ≤ n → ∀ s : ℝ, (M : ℝ) ≤ s →
      sequenceLaw.real {ε | powerSum ε (n + 1) (1 - 1 / s) = 0} < η := by
  have h := uniform_limit_of_admissible_sequences
    (fun n s ↦ sequenceLaw.real {ε | powerSum ε (n + 1) (1 - 1 / s) = 0}) (fun _ _ ↦ True) 0
    (by
      intro n s hn hs _
      exact polynomial_zero_probability_tendsto_zero n _ hn (inverse_scale_point_tendsto s hs 1)
        ((eventually_inverse_scale_point_bounds s hs zero_lt_one).mono (fun _ h ↦ h.2.le)))
  intro η hη
  obtain ⟨M, hM, hb⟩ := h η hη
  refine ⟨M, hM, ?_⟩
  intro n hn s hs
  simpa only [sub_zero, abs_of_nonneg measureReal_nonneg] using hb n hn s hs trivial

end Erdos521
