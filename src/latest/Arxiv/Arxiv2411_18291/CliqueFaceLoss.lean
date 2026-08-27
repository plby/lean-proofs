import Arxiv.Arxiv2411_18291.CliqueSquaredDegrees

/-! # Exact changes in a face degree when a clique is removed -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def cliqueFaceLoss (G : Hypergraph V (r + 1)) (f : Block V r) (Q : Block V q) : ℕ :=
  ((G ∩ cliqueEdges (r + 1) Q).filter fun e => f.val ⊆ e.val).card

theorem clique_face_degree (f : Block V r) (Q : Block V q) :
    ((cliqueEdges (r + 1) Q).filter fun e => f.val ⊆ e.val).card =
      if f.val ⊆ Q.val then q - r else 0 := by
  by_cases hf : f.val ⊆ Q.val
  · rw [if_pos hf]
    have h := card_blocks_between (r := r + 1) f.val Q.val hf
      (by simp only [f.property]; omega)
    simpa [cliqueEdges, filter_filter, and_comm, f.property, Q.property] using h
  · rw [if_neg hf, card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heQ, hfe⟩ := mem_filter.mp he
    exact hf (hfe.trans ((mem_cliqueEdges _ _).mp heQ))

theorem cliqueFaceLoss_le (G : Hypergraph V (r + 1)) (f : Block V r) (Q : Block V q) :
    cliqueFaceLoss G f Q ≤ q - r := by
  have h := card_le_card (filter_subset_filter (fun e : Block V (r + 1) => f.val ⊆ e.val)
    (inter_subset_right (s₁ := G) (s₂ := cliqueEdges (r + 1) Q)))
  rw [clique_face_degree] at h
  exact h.trans (by split_ifs <;> omega)

theorem cliqueFaceLoss_of_clique (G : Hypergraph V (r + 1)) (f : Block V r) (Q : Block V q)
    (hQ : cliqueEdges (r + 1) Q ⊆ G) :
    cliqueFaceLoss G f Q = ((cliqueEdges (r + 1) Q).filter fun e => f.val ⊆ e.val).card := by
  simp only [cliqueFaceLoss, inter_eq_right.mpr hQ]

theorem face_degree_remove_clique (G : Hypergraph V (r + 1)) (f : Block V r) (Q : Block V q) :
    ((G \ cliqueEdges (r + 1) Q).filter fun e => f.val ⊆ e.val).card +
        cliqueFaceLoss G f Q = (G.filter fun e => f.val ⊆ e.val).card := by
  have hs : (G \ cliqueEdges (r + 1) Q).filter (fun e => f.val ⊆ e.val) =
      (G.filter fun e => f.val ⊆ e.val) \ cliqueEdges (r + 1) Q := by
    ext e
    simp only [mem_filter, mem_sdiff]
    tauto
  have hi : (G ∩ cliqueEdges (r + 1) Q).filter (fun e => f.val ⊆ e.val) =
      (G.filter fun e => f.val ⊆ e.val) ∩ cliqueEdges (r + 1) Q := by
    ext e
    simp only [mem_filter, mem_inter]
    tauto
  rw [hs, cliqueFaceLoss, hi]
  exact card_sdiff_add_card_inter _ _

theorem sum_cliqueFaceLoss (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (hH : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) (f : Block V r) :
    (∑ Q ∈ H, (cliqueFaceLoss G f Q : ℝ)) =
      ∑ e ∈ G.filter (fun e => f.val ⊆ e.val),
        ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) := by
  let w : Block V (r + 1) → ℝ := fun e => if f.val ⊆ e.val then 1 else 0
  have hQ : ∀ Q ∈ H, (cliqueFaceLoss G f Q : ℝ) = ∑ e ∈ cliqueEdges (r + 1) Q, w e := by
    intro Q hQ
    rw [cliqueFaceLoss_of_clique G f Q (hH Q hQ)]
    simp only [w, ← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  rw [sum_congr rfl hQ, sum_clique_family_edge_weights]
  have hu : (∑ e ∈ G, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) * w e) =
      ∑ e : Block V (r + 1), ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) * w e := by
    apply sum_subset (subset_univ _)
    intro e _ he
    rw [clique_degree_zero_outside_graph G H hH e he, Nat.cast_zero, zero_mul]
  rw [← hu]
  simp only [w, mul_ite, mul_one, mul_zero, sum_filter]

end Arxiv2411_18291
