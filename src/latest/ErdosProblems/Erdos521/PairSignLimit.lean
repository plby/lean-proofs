/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Weak Gaussian convergence implies convergence of pair sign-change probabilities.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.GaussianPairBoundary
import ErdosProblems.Erdos521.ValuePairLimit

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem pair_sign_probability_tendsto {X : ℕ → (ℕ → ℝ) → EuclideanSpace ℝ (Fin 2)}
    {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1)
    (hX : TendstoInDistribution X atTop (fun x : EuclideanSpace ℝ (Fin 2) ↦ x)
      (fun _ ↦ sequenceLaw) (gaussianPair ρ)) :
    Tendsto (fun n ↦ sequenceLaw.real {ε | (X n ε) 0 * (X n ε) 1 < 0}) atTop
      (𝓝 ((gaussianPair ρ).real pairSignFlip)) := by
  have hnull : ((gaussianPair ρ).map (fun x : EuclideanSpace ℝ (Fin 2) ↦ x))
      (frontier pairSignFlip) = 0 := by
    simpa only [Measure.map_id'] using gaussianPair_signFlip_frontier_null hρ
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hX.tendsto hnull
  have hmap (n : ℕ) : sequenceLaw.map (X n) pairSignFlip =
      sequenceLaw {ε | (X n ε) 0 * (X n ε) 1 < 0} :=
    Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable n) pairSignFlip_measurableSet
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id', hmap] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top (gaussianPair ρ) pairSignFlip)).comp h

end Erdos521
