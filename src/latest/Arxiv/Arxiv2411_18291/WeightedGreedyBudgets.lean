import Arxiv.Arxiv2411_18291.GreedyProbabilityBudget
import Arxiv.Arxiv2411_18291.WeightedFamilyDegrees

/-! # Deterministic probability budgets with fixed root weights

Only the finite sums are expanded. The random embedding associated with a
root is still sampled once, regardless of its weight.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

theorem sum_weighted_rootTargetWeight_le (Φ : I → F ↪ V) (w : I → ℕ)
    (e f : Block W (r + 1)) (hf : f.val ⊆ F) {θ : ℝ}
    (hE : IsWeightedFamilyBounded r (fun i => rootImage (Φ i) f hf) w θ)
    (hθ : 0 ≤ θ) (hn : 0 < Fintype.card V) (he : ¬ e.val ⊆ F) (g : Block V (r + 1)) :
    (∑ i, (w i : ℝ) * rootTargetWeight (Φ i) e f hf g) ≤
      2 * (r + 1).factorial * θ := by
  rw [← sum_weightedIndices w (fun i => rootTargetWeight (Φ i) e f hf g)]
  exact sum_rootTargetWeight_le (fun i : WeightedIndices w => Φ i.1)
      e f hf hE.expanded hθ hn he g

theorem sum_weighted_rootFaceWeight_le (Φ : I → F ↪ V) (w : I → ℕ)
    (e f : Block W (r + 1)) (hf : f.val ⊆ F) {θ : ℝ}
    (hE : IsWeightedFamilyBounded r (fun i => rootImage (Φ i) f hf) w θ)
    (hθ : 0 ≤ θ) (hn : 0 < Fintype.card V) (he : ¬ e.val ⊆ F) (S : Block V r) :
    (∑ i, (w i : ℝ) * rootFaceWeight (Φ i) e f hf S) ≤
      2 * (r + 1).factorial * θ * Fintype.card V := by
  rw [← sum_weightedIndices w (fun i => rootFaceWeight (Φ i) e f hf S)]
  exact sum_rootFaceWeight_le (fun i : WeightedIndices w => Φ i.1)
      e f hf hE.expanded hθ hn he S

end Arxiv2411_18291
