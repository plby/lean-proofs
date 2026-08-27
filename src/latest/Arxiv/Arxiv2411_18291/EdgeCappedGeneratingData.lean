import Arxiv.Arxiv2411_18291.EdgeCappedModularGenerators
import Arxiv.Arxiv2411_18291.ModularGeneratingData

/-! # A good host with simultaneous face and edge caps on its generators

The extra edge saturation contributes an explicit second term to the loss
bound. All generators, saturated cliques, and surviving host edges are
constructed by the finite selection and deletion arguments.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem exists_edge_capped_modular_generating_data (N : ℕ) (hN : 0 < N)
    (K : Hypergraph V (r + 1)) (D : Finset (Block V q))
    (hD : ∀ Q ∈ D, cliqueEdges (r + 1) Q ⊆ K) (faceCap edgeCap : ℕ)
    (hfaceCap : 0 < faceCap) (hedgeCap : 0 < edgeCap) {Lface Ledge μ ε τ : ℝ}
    (hLf : 0 ≤ Lface) (hLe : 0 ≤ Ledge) (hτ : 0 < τ)
    (hface : ∀ S : Block V r, ((D.filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤ Lface)
    (hedge : ∀ e : Block V (r + 1),
      ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ Ledge)
    (hcount : ∀ e ∈ K, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| ≤ ε * μ) :
    ∃ C : ModularGeneratingData K D N,
      (∀ S : Block V r, (C.generators.filter fun Q => S.val ⊆ Q.val).card ≤ faceCap) ∧
      (∀ e : Block V (r + 1),
        (C.generators.filter fun Q => e.val ⊆ Q.val).card ≤ edgeCap) ∧
      C.generators.card ≤ N * K.card ∧
      (C.saturated.card : ℝ) ≤ (q.choose r * (N * K.card) : ℕ) * Lface / faceCap +
        (q.choose (r + 1) * (N * K.card) : ℕ) * Ledge / edgeCap ∧
      ((K \ C.good).card : ℝ) ≤ (q.choose (r + 1) : ℝ) * C.saturated.card / τ ∧
      ∀ e ∈ C.good,
        |(((D \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| < ε * μ + τ := by
  obtain ⟨G, hGD, hfaceG, hedgeG, hsize, hgen⟩ :=
    exists_modular_generators_outside_face_edge_saturation N hN K D hD faceCap edgeCap
  let S := faceEdgeSaturatedCliques D G r faceCap edgeCap
  let C : ModularGeneratingData K D N := {
    generators := G
    saturated := S
    good := goodCliqueEdges K S τ
    generators_subset := hGD
    saturated_subset := faceEdgeSaturatedCliques_subset D G r faceCap edgeCap
    good_subset := filter_subset _ _
    generates := hgen }
  refine ⟨C, hfaceG, hedgeG, hsize, ?_, ?_, ?_⟩
  · exact faceEdgeSaturatedCliques_card_bound D G r faceCap edgeCap (N * K.card)
      hsize hfaceCap hedgeCap hLf hLe hface hedge
  · apply (le_div_iff₀ hτ).mpr
    simpa only [mul_comm] using goodCliqueEdges_bad_count K S τ
  · intro e he
    exact goodCliqueEdges_remaining_error K D S C.saturated_subset hcount he

end Arxiv2411_18291
