import ErdosProblems.Erdos4.FGKMTAggregateBounds
import ErdosProblems.Erdos4.FGKMTAggregateOverlap

/-! Explicit data and error terms for a quantitative covering round. -/

open scoped BigOperators

namespace Erdos4.FGKMT

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

/-- The finite hypotheses for one covering round. Source scales control
both the largest marginal and the sum of squared marginals. -/
structure RoundBounds (μ : I → FiniteLaw (Finset V)) (p : V → ℝ)
    (r : ℕ) (κ δ D : ℝ) where
  kappa_pos : 0 < κ
  kappa_le_one : κ ≤ 1
  delta_nonneg : 0 ≤ δ
  degree_nonneg : 0 ≤ D
  model_lower : ∀ v, κ ≤ p v
  model_upper : ∀ v, p v ≤ 1
  edge_size : ∀ i e, 0 < (μ i).weight e → e.card ≤ r
  source_scale : I → ℝ
  source_marginal : ∀ i v, (μ i).prob (fun e => v ∈ e) ≤ source_scale i
  source_scale_le : ∀ i, source_scale i ≤ δ
  source_scale_sq : (∑ i, source_scale i ^ 2) ≤ δ ^ 2
  pair_degree : ∀ v w, v ≠ w → pairDegree μ v w ≤ δ
  vertex_degree : ∀ v, vertexDegree μ v / p v ≤ D

namespace RoundBounds

variable {μ : I → FiniteLaw (Finset V)} {p : V → ℝ} {r : ℕ} {κ δ D : ℝ}

theorem model_pos (h : RoundBounds μ p r κ δ D) : ∀ v, 0 < p v :=
  fun v => h.kappa_pos.trans_le (h.model_lower v)

theorem sparse (h : RoundBounds μ p r κ δ D) :
    ∀ i v, (μ i).prob (fun e => v ∈ e) ≤ δ :=
  fun i v => (h.source_marginal i v).trans (h.source_scale_le i)

end RoundBounds

noncomputable def roundMeanLoss (r A : ℕ) (κ δ ε t D : ℝ) : ℝ :=
  2 * (normalizationError r κ δ ε t * (A : ℝ) * D / κ ^ r) / κ ^ A +
    (A : ℝ) ^ 2 * δ / κ ^ r +
    (A : ℝ) * (2 * Real.sqrt (degreeVariance r κ δ ε D) / κ ^ A)

noncomputable def roundSquareLoss (r A : ℕ) (κ δ : ℝ) : ℝ :=
  4 * (A : ℝ) ^ 2 * δ ^ 2 / κ ^ (2 * r)

noncomputable def roundLoss (r A : ℕ) (κ δ ε t D : ℝ) : ℝ :=
  roundMeanLoss r A κ δ ε t D + roundSquareLoss r A κ δ

theorem roundMeanLoss_nonneg (r A : ℕ) {κ δ ε t D : ℝ}
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (ht : 0 ≤ t) (hD : 0 ≤ D) :
    0 ≤ roundMeanLoss r A κ δ ε t D := by
  have hK := normalizationError_nonneg r hκ hδ hε ht
  unfold roundMeanLoss
  positivity

theorem roundSquareLoss_nonneg (r A : ℕ) {κ δ : ℝ} (hκ : 0 < κ) :
    0 ≤ roundSquareLoss r A κ δ := by
  unfold roundSquareLoss
  positivity

theorem roundLoss_nonneg (r A : ℕ) {κ δ ε t D : ℝ}
    (hκ : 0 < κ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (ht : 0 ≤ t) (hD : 0 ≤ D) :
    0 ≤ roundLoss r A κ δ ε t D :=
  add_nonneg (roundMeanLoss_nonneg r A hκ hδ hε ht hD) (roundSquareLoss_nonneg r A hκ)

end Erdos4.FGKMT
