/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Gaussian limits for pairs of normalized weighted sign sums.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.PairWeights
import ErdosProblems.Erdos521.VectorCentralLimit

namespace Erdos521

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology InnerProductSpace

theorem pair_projected_variance_tendsto (S : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℝ) {ρ : ℝ}
    (hρ : ρ ^ 2 ≤ 1)
    (ha : Tendsto (fun n ↦ ∑ i ∈ S n, a n i ^ 2) atTop (𝓝 1))
    (hb : Tendsto (fun n ↦ ∑ i ∈ S n, b n i ^ 2) atTop (𝓝 1))
    (hab : Tendsto (fun n ↦ ∑ i ∈ S n, a n i * b n i) atTop (𝓝 ρ))
    (t : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun n ↦ ∑ i ∈ S n, ⟪!₂[a n i, b n i], t⟫_ℝ ^ 2) atTop
      (𝓝 (covarianceBilin (gaussianPair ρ) t t)) := by
  simp_rw [pair_projected_variance]
  rw [gaussianPair_covariance hρ]
  have h := ((ha.const_mul (t 0 ^ 2)).add (hab.const_mul (2 * t 0 * t 1))).add
    (hb.const_mul (t 1 ^ 2))
  convert h using 1
  congr 1
  ring

theorem triangular_pair_sign_central_limit (S : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℝ) {ρ : ℝ}
    (hρ : ρ ^ 2 ≤ 1)
    (hsmallA : ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ S n, |a n i| < r)
    (hsmallB : ∀ r : ℝ, 0 < r → ∀ᶠ n : ℕ in atTop, ∀ i ∈ S n, |b n i| < r)
    (ha : Tendsto (fun n ↦ ∑ i ∈ S n, a n i ^ 2) atTop (𝓝 1))
    (hb : Tendsto (fun n ↦ ∑ i ∈ S n, b n i ^ 2) atTop (𝓝 1))
    (hab : Tendsto (fun n ↦ ∑ i ∈ S n, a n i * b n i) atTop (𝓝 ρ)) :
    TendstoInDistribution (fun n ε ↦ ∑ i ∈ S n, ε i • !₂[a n i, b n i]) atTop
      (fun x : EuclideanSpace ℝ (Fin 2) ↦ x) (fun _ ↦ sequenceLaw) (gaussianPair ρ) :=
  triangular_vector_sign_central_limit S (fun n i ↦ !₂[a n i, b n i]) (gaussianPair ρ)
    (gaussianPair_mean ρ) (pair_projected_weights_small S a b hsmallA hsmallB)
    (pair_projected_variance_tendsto S a b hρ ha hb hab)

end Erdos521
