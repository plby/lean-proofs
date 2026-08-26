/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The joint Gaussian limit for two normalized Littlewood evaluations.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.PairCentralLimit
import ErdosProblems.Erdos521.NormalizedWeights

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem pair_sign_sum_eq (S : Finset ℕ) (a b ε : ℕ → ℝ) :
    (∑ i ∈ S, ε i • !₂[a i, b i]) = !₂[∑ i ∈ S, a i * ε i, ∑ i ∈ S, b i * ε i] := by
  ext k
  fin_cases k <;> simp [mul_comm]

theorem polynomial_value_pair_central_limit (d : ℕ → ℕ) (s : ℕ → ℝ)
    (hd : Tendsto d atTop atTop) (hs : Tendsto s atTop atTop)
    (hN : Tendsto (fun j ↦ ((d j + 1 : ℕ) : ℝ) / s j) atTop atTop)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    TendstoInDistribution (fun j ε ↦
      !₂[powerSum ε (d j + 1) (1 - a / s j) / Real.sqrt (geometricVariance (1 - a / s j) (d j + 1)),
        powerSum ε (d j + 1) (1 - b / s j) / Real.sqrt (geometricVariance (1 - b / s j) (d j + 1))])
      atTop (fun x : EuclideanSpace ℝ (Fin 2) ↦ x) (fun _ ↦ sequenceLaw)
      (gaussianPair (2 * Real.sqrt (a * b) / (a + b))) := by
  let S := fun j ↦ Finset.range (d j + 1)
  let A := fun j i ↦ (1 - a / s j) ^ i / Real.sqrt (geometricVariance (1 - a / s j) (d j + 1))
  let B := fun j i ↦ (1 - b / s j) ^ i / Real.sqrt (geometricVariance (1 - b / s j) (d j + 1))
  have hsmall (c : ℝ) (hc : 0 < c) (r : ℝ) (hr : 0 < r) :
      ∀ᶠ j : ℕ in atTop, ∀ i ∈ S j,
        |(1 - c / s j) ^ i / Real.sqrt (geometricVariance (1 - c / s j) (d j + 1))| < r := by
    have hI : ∀ᶠ j : ℕ in atTop, 0 ≤ 1 - c / s j ∧ 1 - c / s j ≤ 1 :=
      (eventually_inverse_scale_point_bounds s hs hc).mono (fun _ hj ↦ ⟨hj.1, hj.2.le⟩)
    exact (normalized_geometric_weights_small d _ hd (inverse_scale_point_tendsto s hs c) hI r hr).mono
      (fun _ hj i _ ↦ hj i)
  have hvariance (c : ℝ) : Tendsto (fun j ↦ ∑ i ∈ S j,
      ((1 - c / s j) ^ i / Real.sqrt (geometricVariance (1 - c / s j) (d j + 1))) ^ 2) atTop (𝓝 1) := by
    simp only [S, normalized_geometric_variance_sum]
    exact tendsto_const_nhds
  have h := triangular_pair_sign_central_limit S A B (inverse_scale_correlation_sq_le_one ha hb)
    (hsmall a ha) (hsmall b hb) (hvariance a) (hvariance b)
    (normalized_geometric_weight_product_tendsto (fun j ↦ d j + 1) s hs hN ha hb)
  apply h.congr _ (Filter.Eventually.of_forall (fun _ ↦ rfl))
  intro j
  filter_upwards [] with ε
  rw [pair_sign_sum_eq]
  ext k
  fin_cases k <;> simp [S, A, B, powerSum, Finset.sum_div, mul_comm, ← mul_div_assoc]

end Erdos521
