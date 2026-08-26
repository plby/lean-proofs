import ErdosProblems.Erdos73.BrickFaceArray
import ErdosProblems.Erdos73.SubdivisionAnchors

/-! Face-strip supports and the two-row/two-column membership bound. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} {c r : ℕ}

def brickFaceRowStrip (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a : Fin (r - 1)) : Finset V := Finset.univ.biUnion fun j => brickFaceRegion S (a, j)

def brickFaceColumnStrip (S : GraphSubdivisionModel (elementaryWall c r) G)
    (j : Fin (c - 1)) : Finset V := Finset.univ.biUnion fun a => brickFaceRegion S (a, j)

theorem brickFaceRegion_subset (S : GraphSubdivisionModel (elementaryWall c r) G)
    (i : Fin (r - 1) × Fin (c - 1)) : brickFaceRegion S i ⊆ S.vertexSet :=
  S.restrictCopy_vertexSet_subset_vertexSet _

theorem brickFaceRowStrip_subset (S : GraphSubdivisionModel (elementaryWall c r) G)
    (a : Fin (r - 1)) : brickFaceRowStrip S a ⊆ S.vertexSet := by
  intro x hx
  obtain ⟨j, _, hx⟩ := mem_biUnion.mp hx
  exact brickFaceRegion_subset S (a, j) hx

theorem brickFaceColumnStrip_subset (S : GraphSubdivisionModel (elementaryWall c r) G)
    (j : Fin (c - 1)) : brickFaceColumnStrip S j ⊆ S.vertexSet := by
  intro x hx
  obtain ⟨a, _, hx⟩ := mem_biUnion.mp hx
  exact brickFaceRegion_subset S (a, j) hx

theorem anchor_bounds_of_mem_brickFaceRegion
    (S : GraphSubdivisionModel (elementaryWall c r) G) (x : {v : V // v ∈ S.vertexSet})
    (a : Fin (r - 1)) (j : Fin (c - 1)) (hx : x.val ∈ brickFaceRegion S (a, j)) :
    a.val ≤ (S.supportAnchor x).val.1.val ∧ (S.supportAnchor x).val.1.val ≤ a.val + 1 ∧
      brickFaceColumn a.val j.val ≤ (S.supportAnchor x).val.2.val ∧
      (S.supportAnchor x).val.2.val ≤ brickFaceColumn a.val j.val + 2 := by
  classical
  obtain ⟨i, hi⟩ := S.exists_supportAnchor_restrict_preimage
    (elementaryBrickFaceCopy a.val (brickFaceColumn a.val j.val) _ _ _) x hx
  have hrow := congrArg (fun v : ElementaryWallVertex c r => v.val.1.val) hi
  have hcol := congrArg (fun v : ElementaryWallVertex c r => v.val.2.val) hi
  change a.val + (brickFacePosition i).1 = (S.supportAnchor x).val.1.val at hrow
  change brickFaceColumn a.val j.val + (brickFacePosition i).2 =
    (S.supportAnchor x).val.2.val at hcol
  have hb := brickFacePosition_bounds i
  omega

theorem card_finset_fin_le_two_of_values {n : ℕ} (A : Finset (Fin n)) (a b : ℕ)
    (hA : ∀ i ∈ A, i.val = a ∨ i.val = b) : A.card ≤ 2 := by
  have hsub : A.image Fin.val ⊆ {a, b} := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    rcases hA i hi with he | he <;> simp [he]
  have hh := card_le_card hsub
  rw [card_image_of_injective _ Fin.val_injective] at hh
  have hp : ({a, b} : Finset ℕ).card ≤ 2 := by
    by_cases he : a = b <;> simp [he]
  exact hh.trans hp

theorem brickFaceRowStrip_membership_card_le_two
    (S : GraphSubdivisionModel (elementaryWall c r) G) (x : V) :
    (Finset.univ.filter (fun a => x ∈ brickFaceRowStrip S a)).card ≤ 2 := by
  by_cases hxS : x ∈ S.vertexSet
  · let z : {v : V // v ∈ S.vertexSet} := ⟨x, hxS⟩
    let a := (S.supportAnchor z).val.1.val
    apply card_finset_fin_le_two_of_values _ a (a - 1)
    intro i hi
    obtain ⟨j, _, hx⟩ := mem_biUnion.mp (mem_filter.mp hi).2
    have hb := anchor_bounds_of_mem_brickFaceRegion S z i j hx
    change i.val ≤ a ∧ a ≤ i.val + 1 ∧ _ at hb
    omega
  · have he : Finset.univ.filter (fun a => x ∈ brickFaceRowStrip S a) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro a _ hx
      exact hxS (brickFaceRowStrip_subset S a hx)
    rw [he]
    simp only [card_empty, Nat.zero_le]

theorem brickFaceColumnStrip_membership_card_le_two
    (S : GraphSubdivisionModel (elementaryWall c r) G) (x : V) :
    (Finset.univ.filter (fun j => x ∈ brickFaceColumnStrip S j)).card ≤ 2 := by
  by_cases hxS : x ∈ S.vertexSet
  · let z : {v : V // v ∈ S.vertexSet} := ⟨x, hxS⟩
    let b := (S.supportAnchor z).val.2.val / 2
    apply card_finset_fin_le_two_of_values _ b (b - 1)
    intro j hj
    obtain ⟨a, _, hx⟩ := mem_biUnion.mp (mem_filter.mp hj).2
    have hb := (anchor_bounds_of_mem_brickFaceRegion S z a j hx).2.2
    dsimp only [brickFaceColumn] at hb
    dsimp only [b]
    omega
  · have he : Finset.univ.filter (fun j => x ∈ brickFaceColumnStrip S j) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro j _ hx
      exact hxS (brickFaceColumnStrip_subset S j hx)
    rw [he]
    simp only [card_empty, Nat.zero_le]

end
end Erdos73
