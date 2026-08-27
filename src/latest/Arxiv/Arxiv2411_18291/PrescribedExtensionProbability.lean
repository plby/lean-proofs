import Arxiv.Arxiv2411_18291.PrescribedEmbeddingCount
import Arxiv.Arxiv2411_18291.GreedyStepExpectation

/-!
# Probability budgets for prescribed extensions

Restricting to a candidate family of relative size `η` costs a factor `η⁻¹`
in the one-step probability estimate. Compatibility with the fixed roots is
unchanged, so the same factor is the only change in the cumulative budget.
-/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

theorem uniformExtensions_target_probability_le_weight_scaled (φ : F ↪ V)
    [MeasurableSpace (EmbeddingExtension φ)] [MeasurableSingletonClass (EmbeddingExtension φ)]
    (s : Finset (EmbeddingExtension φ)) (hs : s.Nonempty) {η : ℝ} (hη : 0 < η)
    (hcount : (η / 2) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ s.card)
    (hn : 0 < Fintype.card V) (e f : Block W (r + 1))
    (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val) (g : Block V (r + 1)) :
    (PMF.uniformOfFinset s hs).toMeasure.real {a | mapBlock a.val e = g} ≤
      rootTargetWeight φ e f hf g / η := by
  unfold rootTargetWeight
  split_ifs with h
  · exact uniformExtensions_target_probability_le_scaled φ s hs hη hcount hn e g
  · have he : {a : EmbeddingExtension φ | mapBlock a.val e = g} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact h (rootImage_overlap_of_target φ e f hf hcover a g ha)
    rw [he, measureReal_empty, zero_div]

theorem uniformExtensions_face_probability_le_weight_scaled (φ : F ↪ V)
    [MeasurableSpace (EmbeddingExtension φ)] [MeasurableSingletonClass (EmbeddingExtension φ)]
    (s : Finset (EmbeddingExtension φ)) (hs : s.Nonempty) {η : ℝ} (hη : 0 < η)
    (hcount : (η / 2) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ s.card)
    (hn : 0 < Fintype.card V) (e f : Block W (r + 1))
    (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val) (S : Block V r) :
    (PMF.uniformOfFinset s hs).toMeasure.real {a | S.val ⊆ (mapBlock a.val e).val} ≤
      rootFaceWeight φ e f hf S / η := by
  apply (embeddingExtension_face_probability_le_sum φ _ e S).trans
  rw [rootFaceWeight, sum_div]
  exact sum_le_sum fun g _ =>
    uniformExtensions_target_probability_le_weight_scaled φ s hs hη hcount hn e f hf hcover g

theorem uniformExtension_state_mean_le_scaled (φ : F ↪ V)
    (s : Finset (EmbeddingExtension φ)) (hs : s.Nonempty) {η : ℝ} (hη : 0 < η)
    (hcount : (η / 2) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤ s.card)
    (hn : 0 < Fintype.card V) (e f : Block W (r + 1))
    (hf : f.val ⊆ F) (hcover : e.val ∩ F ⊆ f.val) (S : Block V r) :
    (∫ a, stateFaceIndicator a e S.val
      ∂((PMF.uniformOfFinset s hs).map (fun f => chosenEmbedding f.val)).toMeasure) ≤
      rootFaceWeight φ e f hf S / η := by
  let : MeasurableSpace (EmbeddingExtension φ) := ⊤
  rw [uniformExtension_state_mean_eq φ s hs e S.val]
  exact uniformExtensions_face_probability_le_weight_scaled φ s hs hη hcount hn e f hf hcover S

variable {I : Type*} [Fintype I]

omit [Fintype W] in
theorem sum_rootFaceWeight_scaled_le (Φ : I → F ↪ V) (e f : Block W (r + 1))
    (hf : f.val ⊆ F) {θ η : ℝ} (hE : IsEdgeFamilyBounded (fun i => rootImage (Φ i) f hf) θ)
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hn : 0 < Fintype.card V) (he : ¬ e.val ⊆ F) (S : Block V r) :
    (∑ i, rootFaceWeight (Φ i) e f hf S / η) ≤
      (2 * (r + 1).factorial * θ * Fintype.card V) / η := by
  rw [← sum_div]
  exact div_le_div_of_nonneg_right (sum_rootFaceWeight_le Φ e f hf hE hθ hn he S) hη

end Arxiv2411_18291
