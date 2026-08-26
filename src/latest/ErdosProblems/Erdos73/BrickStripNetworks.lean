import ErdosProblems.Erdos73.BrickFaceStrips

/-! Selected nonempty families of face-row and face-column strips form robust networks. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

section General
variable [DecidableEq V]

theorem DeletionOneConnected.two_le_card {D : Finset V}
    (hD : DeletionOneConnected G D) : 2 ≤ D.card := by
  by_contra hn
  obtain ⟨x⟩ := (hD D (by omega)).nonempty
  exact (mem_sdiff.mp x.property).2 (mem_sdiff.mp x.property).1

theorem DeletionOneConnected.union_biUnion {I : Type*} [DecidableEq I]
    {D : Finset V} (hD : DeletionOneConnected G D) (A : Finset I) (R : I → Finset V)
    (hR : ∀ i ∈ A, DeletionOneConnected G (R i))
    (hover : ∀ i ∈ A, 2 ≤ (D ∩ R i).card) :
    DeletionOneConnected G (D ∪ A.biUnion R) := by
  induction A using Finset.induction_on with
  | empty => simpa using hD
  | @insert i A hi ih =>
    have hA := ih (fun j hj => hR j (mem_insert_of_mem hj))
      (fun j hj => hover j (mem_insert_of_mem hj))
    have hcard : 2 ≤ ((D ∪ A.biUnion R) ∩ R i).card :=
      (hover i (mem_insert_self _ _)).trans (card_le_card
        (inter_subset_inter subset_union_left subset_rfl))
    have hh := hA.union (hR i (mem_insert_self _ _)) hcard
    simpa only [biUnion_insert, union_assoc, union_comm, union_left_comm] using hh

end General

variable {c r : ℕ}

theorem brickFaceRowStrip_robust (S : GraphSubdivisionModel (elementaryWall c r) G)
    (hc : 2 ≤ c) (a : Fin (r - 1)) : DeletionOneConnected G (brickFaceRowStrip S a) := by
  have : NeZero (c - 1) := ⟨by omega⟩
  apply deletionOneConnected_biUnion (fun j => brickFaceRegion S (a, j))
    (fun j => brickFaceRegion_robust S (a, j))
    (show (pathGraph (c - 1)).Connected from ⟨pathGraph_preconnected _⟩)
  intro i j hij
  rcases pathGraph_adj.mp hij with hij | hij
  · exact brickFaceRegion_horizontal_overlap S a i j hij
  · rw [inter_comm]
    exact brickFaceRegion_horizontal_overlap S a j i hij

theorem brickFaceColumnStrip_robust (S : GraphSubdivisionModel (elementaryWall c r) G)
    (hr : 2 ≤ r) (j : Fin (c - 1)) : DeletionOneConnected G (brickFaceColumnStrip S j) := by
  have : NeZero (r - 1) := ⟨by omega⟩
  apply deletionOneConnected_biUnion (fun a => brickFaceRegion S (a, j))
    (fun a => brickFaceRegion_robust S (a, j))
    (show (pathGraph (r - 1)).Connected from ⟨pathGraph_preconnected _⟩)
  intro a b hab
  rcases pathGraph_adj.mp hab with hab | hab
  · exact brickFaceRegion_vertical_overlap S a b j hab
  · rw [inter_comm]
    exact brickFaceRegion_vertical_overlap S b a j hab

theorem brickFaceRowColumnStrip_overlap (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a : Fin (r - 1)) (j : Fin (c - 1)) :
    2 ≤ (brickFaceRowStrip S a ∩ brickFaceColumnStrip S j).card := by
  apply (brickFaceRegion_robust S (a, j)).two_le_card.trans
  apply card_le_card
  intro x hx
  exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨j, mem_univ _, hx⟩,
    mem_biUnion.mpr ⟨a, mem_univ _, hx⟩⟩

def brickStripNetwork (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1))) : Finset V :=
  A.biUnion (brickFaceRowStrip S) ∪ B.biUnion (brickFaceColumnStrip S)

theorem mem_brickStripNetwork (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1))) (x : V) :
    x ∈ brickStripNetwork S A B ↔
      (∃ a ∈ A, x ∈ brickFaceRowStrip S a) ∨
      (∃ j ∈ B, x ∈ brickFaceColumnStrip S j) := by
  simp only [brickStripNetwork, mem_union, mem_biUnion]

theorem brickStripNetwork_subset (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1))) :
    brickStripNetwork S A B ⊆ S.vertexSet := by
  intro x hx
  rcases (mem_brickStripNetwork S A B x).mp hx with ⟨a, _, ha⟩ | ⟨j, _, hj⟩
  · exact brickFaceRowStrip_subset S a ha
  · exact brickFaceColumnStrip_subset S j hj

theorem brickStripNetwork_robust (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : Finset (Fin (r - 1))) (B : Finset (Fin (c - 1)))
    (hA : A.Nonempty) (hB : B.Nonempty) : DeletionOneConnected G (brickStripNetwork S A B) := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hr : 2 ≤ r := by have hh := a.isLt; omega
  have hc : 2 ≤ c := by have hh := b.isLt; omega
  have hfirst : DeletionOneConnected G
      (brickFaceColumnStrip S b ∪ A.biUnion (brickFaceRowStrip S)) := by
    apply (brickFaceColumnStrip_robust S hr b).union_biUnion
    · exact fun i _ => brickFaceRowStrip_robust S hc i
    · intro i _
      rw [inter_comm]
      exact brickFaceRowColumnStrip_overlap S i b
  have hsecond := hfirst.union_biUnion B (brickFaceColumnStrip S)
    (fun j _ => brickFaceColumnStrip_robust S hr j) (by
      intro j _
      apply (brickFaceRowColumnStrip_overlap S a j).trans
      apply card_le_card
      apply inter_subset_inter _ subset_rfl
      intro x hx
      exact mem_union_right _ (mem_biUnion.mpr ⟨a, ha, hx⟩))
  have he : (brickFaceColumnStrip S b ∪ A.biUnion (brickFaceRowStrip S)) ∪
      B.biUnion (brickFaceColumnStrip S) = brickStripNetwork S A B := by
    ext x
    have hh : x ∈ brickFaceColumnStrip S b → x ∈ B.biUnion (brickFaceColumnStrip S) :=
      fun hx => mem_biUnion.mpr ⟨b, hb, hx⟩
    simp only [brickStripNetwork, mem_union]
    tauto
  exact he ▸ hsecond

end
end Erdos73
