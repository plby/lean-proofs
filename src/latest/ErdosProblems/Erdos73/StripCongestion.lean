import ErdosProblems.Erdos73.BrickStripNetworks

/-! Disjoint choices of strip indices retain the fourfold network congestion bound. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

theorem biUnion_membership_card_le_of_pairwise_disjoint
    {I J V : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [DecidableEq V]
    (D : I → Finset J) (R : J → Finset V)
    (hD : Pairwise (fun i j => Disjoint (D i) (D j))) (x : V) :
    (Finset.univ.filter (fun i => x ∈ (D i).biUnion R)).card ≤
      (Finset.univ.filter (fun j => x ∈ R j)).card := by
  let A := Finset.univ.filter (fun i => x ∈ (D i).biUnion R)
  let B := Finset.univ.filter (fun j => x ∈ R j)
  have hex (i : A) : ∃ j, j ∈ D i.val ∧ x ∈ R j :=
    mem_biUnion.mp (mem_filter.mp i.property).2
  let f : A → B := fun i => ⟨(hex i).choose,
    mem_filter.mpr ⟨mem_univ _, (hex i).choose_spec.2⟩⟩
  apply card_le_card_of_injective (f := f)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he : (hex i).choose = (hex j).choose := congrArg Subtype.val hij
  exact disjoint_left.mp (hD hne) (hex i).choose_spec.1
    (he ▸ (hex j).choose_spec.1)

variable {V : Type*} {G : SimpleGraph V} {c r : ℕ}

theorem brickStripNetwork_membership_card_le_four {I : Type*} [Fintype I]
    (S : GraphSubdivisionModel (elementaryWall c r) G)
    (A : I → Finset (Fin (r - 1))) (B : I → Finset (Fin (c - 1)))
    (hA : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hB : Pairwise (fun i j => Disjoint (B i) (B j))) (x : V) :
    (Finset.univ.filter (fun i => x ∈ brickStripNetwork S (A i) (B i))).card ≤ 4 := by
  have hrow := (biUnion_membership_card_le_of_pairwise_disjoint A (brickFaceRowStrip S) hA x).trans
    (brickFaceRowStrip_membership_card_le_two S x)
  have hcol := (biUnion_membership_card_le_of_pairwise_disjoint B (brickFaceColumnStrip S) hB x).trans
    (brickFaceColumnStrip_membership_card_le_two S x)
  have hsub : Finset.univ.filter (fun i => x ∈ brickStripNetwork S (A i) (B i)) ⊆
      Finset.univ.filter (fun i => x ∈ (A i).biUnion (brickFaceRowStrip S)) ∪
      Finset.univ.filter (fun i => x ∈ (B i).biUnion (brickFaceColumnStrip S)) := by
    intro i hi
    rcases mem_union.mp (mem_filter.mp hi).2 with hi | hi
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hi⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hi⟩)
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  omega

theorem union_disjoint_supports_membership_card_le_add_one
    {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (D U : I → Finset V) (hU : Pairwise (fun i j => Disjoint (U i) (U j)))
    (t : ℕ) (hD : ∀ x, (Finset.univ.filter (fun i => x ∈ D i)).card ≤ t) (x : V) :
    (Finset.univ.filter (fun i => x ∈ D i ∪ U i)).card ≤ t + 1 := by
  have hUc : (Finset.univ.filter (fun i => x ∈ U i)).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    by_contra hn
    exact disjoint_left.mp (hU hn) (mem_filter.mp hi).2 (mem_filter.mp hj).2
  have hsub : Finset.univ.filter (fun i => x ∈ D i ∪ U i) ⊆
      Finset.univ.filter (fun i => x ∈ D i) ∪ Finset.univ.filter (fun i => x ∈ U i) := by
    intro i hi
    rcases mem_union.mp (mem_filter.mp hi).2 with hi | hi
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hi⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hi⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add (hD x) hUc))

end
end Erdos73
