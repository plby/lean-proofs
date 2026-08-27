import Arxiv.Arxiv2411_18291.GoodCliqueEdges

/-! # Modular generators with separate face and edge caps

The same finite maximality argument can constrain both face degrees and
edge multiplicities. Only cliques saturated in at least one of the two
senses can remain outside the generated subgroup.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def faceEdgeIncidence (Q : Block V q) : (Block V r ⊕ Block V (r + 1)) → Prop
  | Sum.inl S => S.val ⊆ Q.val
  | Sum.inr e => e.val ⊆ Q.val

instance decidableFaceEdgeIncidence :
    DecidableRel (faceEdgeIncidence (V := V) (q := q) (r := r)) :=
  fun Q t => match t with
    | Sum.inl S => inferInstanceAs (Decidable (S.val ⊆ Q.val))
    | Sum.inr e => inferInstanceAs (Decidable (e.val ⊆ Q.val))

theorem exists_modular_generators_with_face_edge_caps (N : ℕ) (hN : 0 < N)
    (K : Hypergraph V (r + 1)) (D : Finset (Block V q))
    (hD : ∀ Q ∈ D, cliqueEdges (r + 1) Q ⊆ K) (faceCap edgeCap : ℕ) :
    ∃ G : Finset (Block V q), G ⊆ D ∧
      (∀ S : Block V r, (G.filter fun Q => S.val ⊆ Q.val).card ≤ faceCap) ∧
      (∀ e : Block V (r + 1), (G.filter fun Q => e.val ⊆ Q.val).card ≤ edgeCap) ∧
      G.card ≤ N * K.card ∧
      ∀ Q ∈ D,
        (∀ S : Block V r, S.val ⊆ Q.val →
          (G.filter fun R => S.val ⊆ R.val).card < faceCap) →
        (∀ e : Block V (r + 1), e.val ⊆ Q.val →
          (G.filter fun R => e.val ⊆ R.val).card < edgeCap) →
        modularCliqueVector N (r + 1) Q ∈ generatedSubgroup (modularCliqueVector N (r + 1)) G := by
  obtain ⟨G, hGD, hload, hsize, hgen⟩ :=
    exists_modular_generating_cliques_with_caps N hN K D hD (faceEdgeIncidence (r := r))
      (Sum.elim (fun _ => faceCap) (fun _ => edgeCap))
  have hf (S : Block V r) :
      G.filter (fun Q => faceEdgeIncidence (r := r) Q (Sum.inl S)) =
        G.filter (fun Q => S.val ⊆ Q.val) := by
    ext Q
    rw [mem_filter, mem_filter]
    rfl
  have he (e : Block V (r + 1)) :
      G.filter (fun Q => faceEdgeIncidence (r := r) Q (Sum.inr e)) =
        G.filter (fun Q => e.val ⊆ Q.val) := by
    ext Q
    rw [mem_filter, mem_filter]
    rfl
  refine ⟨G, hGD, ?_, ?_, hsize, ?_⟩
  · intro S
    simpa only [hf, Sum.elim_inl] using hload (Sum.inl S)
  · intro e
    simpa only [he, Sum.elim_inr] using hload (Sum.inr e)
  · intro Q hQ hface hedge
    apply hgen Q hQ
    intro t ht
    cases t with
    | inl S =>
      have hh := hface S ht
      rw [← hf S] at hh
      exact hh
    | inr e =>
      have hh := hedge e ht
      rw [← he e] at hh
      exact hh

def faceEdgeSaturatedCliques (D G : Finset (Block V q)) (r faceCap edgeCap : ℕ) :=
  saturatedCliques D G r faceCap ∪ saturatedCliques D G (r + 1) edgeCap

theorem faceEdgeSaturatedCliques_subset (D G : Finset (Block V q))
    (r faceCap edgeCap : ℕ) : faceEdgeSaturatedCliques D G r faceCap edgeCap ⊆ D :=
  union_subset (filter_subset _ _) (filter_subset _ _)

theorem exists_modular_generators_outside_face_edge_saturation (N : ℕ) (hN : 0 < N)
    (K : Hypergraph V (r + 1)) (D : Finset (Block V q))
    (hD : ∀ Q ∈ D, cliqueEdges (r + 1) Q ⊆ K) (faceCap edgeCap : ℕ) :
    ∃ G : Finset (Block V q), G ⊆ D ∧
      (∀ S : Block V r, (G.filter fun Q => S.val ⊆ Q.val).card ≤ faceCap) ∧
      (∀ e : Block V (r + 1), (G.filter fun Q => e.val ⊆ Q.val).card ≤ edgeCap) ∧
      G.card ≤ N * K.card ∧
      ∀ Q ∈ D \ faceEdgeSaturatedCliques D G r faceCap edgeCap,
        modularCliqueVector N (r + 1) Q ∈ generatedSubgroup (modularCliqueVector N (r + 1)) G := by
  obtain ⟨G, hGD, hface, hedge, hsize, hgen⟩ :=
    exists_modular_generators_with_face_edge_caps N hN K D hD faceCap edgeCap
  refine ⟨G, hGD, hface, hedge, hsize, ?_⟩
  intro Q hQ
  obtain ⟨hQD, hnot⟩ := mem_sdiff.mp hQ
  apply hgen Q hQD
  · intro S hSQ
    by_contra hs
    exact hnot (mem_union_left _ (mem_filter.mpr
      ⟨hQD, S, mem_filter.mpr ⟨mem_univ _, Nat.le_of_not_gt hs⟩, hSQ⟩))
  · intro e heQ
    by_contra he
    exact hnot (mem_union_right _ (mem_filter.mpr
      ⟨hQD, e, mem_filter.mpr ⟨mem_univ _, Nat.le_of_not_gt he⟩, heQ⟩))

theorem faceEdgeSaturatedCliques_card_bound (D G : Finset (Block V q))
    (r faceCap edgeCap M : ℕ) (hG : G.card ≤ M)
    (hfaceCap : 0 < faceCap) (hedgeCap : 0 < edgeCap) {Lface Ledge : ℝ}
    (hLf : 0 ≤ Lface) (hLe : 0 ≤ Ledge)
    (hface : ∀ S : Block V r, ((D.filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤ Lface)
    (hedge : ∀ e : Block V (r + 1),
      ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ Ledge) :
    ((faceEdgeSaturatedCliques D G r faceCap edgeCap).card : ℝ) ≤
      (q.choose r * M : ℕ) * Lface / faceCap +
        (q.choose (r + 1) * M : ℕ) * Ledge / edgeCap := by
  have hf : ((saturatedCliques D G r faceCap).card : ℝ) ≤
      (q.choose r * M : ℕ) * Lface / faceCap := by
    apply (le_div_iff₀ (by exact_mod_cast hfaceCap : (0 : ℝ) < faceCap)).mpr
    simpa only [mul_comm] using
      saturatedCliques_weighted_bound D G r faceCap M hG hLf (fun S _ => hface S)
  have he : ((saturatedCliques D G (r + 1) edgeCap).card : ℝ) ≤
      (q.choose (r + 1) * M : ℕ) * Ledge / edgeCap := by
    apply (le_div_iff₀ (by exact_mod_cast hedgeCap : (0 : ℝ) < edgeCap)).mpr
    simpa only [mul_comm] using
      saturatedCliques_weighted_bound D G (r + 1) edgeCap M hG hLe (fun e _ => hedge e)
  have hu : ((faceEdgeSaturatedCliques D G r faceCap edgeCap).card : ℝ) ≤
      (saturatedCliques D G r faceCap).card + (saturatedCliques D G (r + 1) edgeCap).card := by
    exact_mod_cast card_union_le (saturatedCliques D G r faceCap)
      (saturatedCliques D G (r + 1) edgeCap)
  linarith only [hf, he, hu]

end Arxiv2411_18291
