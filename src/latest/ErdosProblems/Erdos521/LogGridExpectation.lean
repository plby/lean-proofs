/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The Gaussian limit of the expected sign count on a fixed logarithmic grid.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LogGrid
import ErdosProblems.Erdos521.SignGridExpectation
import ErdosProblems.Erdos521.PolynomialSignProbability

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem logGrid_sign_expectation_tendsto (n : ℕ → ℕ) (s : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hs : Tendsto s atTop atTop)
    (hN : Tendsto (fun j ↦ ((n j + 1 : ℕ) : ℝ) / s j) atTop atTop)
    {a : ℝ} (ha : 0 < a) (δ : ℝ) (N : ℕ) :
    Tendsto (fun j ↦ ∫ ε, (gridSignChanges ε (n j) (logGrid (s j) a δ) N : ℝ) ∂sequenceLaw)
      atTop (𝓝 ((N : ℝ) * (gaussianPair (logScaleCorrelation δ)).real pairSignFlip)) := by
  simp_rw [integral_gridSignChanges]
  have hcell (i : ℕ) : Tendsto (fun j ↦ sequenceLaw.real {ε |
      powerSum ε (n j + 1) (logGrid (s j) a δ i) *
        powerSum ε (n j + 1) (logGrid (s j) a δ (i + 1)) < 0}) atTop
      (𝓝 ((gaussianPair (logScaleCorrelation δ)).real pairSignFlip)) := by
    have h := polynomial_sign_probability_tendsto n s hn hs hN
      (logGridCoefficient_pos ha δ i) (logGridCoefficient_pos ha δ (i + 1))
    rw [logGrid_correlation ha] at h
    exact h
  have h := tendsto_finsetSum (Finset.range N) (fun i _ ↦ hcell i)
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

end Erdos521
