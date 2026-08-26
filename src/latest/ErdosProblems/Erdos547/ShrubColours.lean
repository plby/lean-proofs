import ErdosProblems.Erdos547.FineTreePartition

/-!
# The two shrub families and their four bipartition parts
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}

noncomputable def shrubsOfColour (P : FineTreePartition T r ℓ col) (i : Fin 2) :
    Finset (Finset U) :=
  by classical exact P.shrubs.filter (fun C ↦ ∀ z ∈ P.seeds, 0 < degreeIn T C z → col z = i)

noncomputable def shrubVertices (P : FineTreePartition T r ℓ col) (i : Fin 2) : Finset U :=
  (P.shrubsOfColour i).biUnion id

noncomputable def nearVertices (P : FineTreePartition T r ℓ col) (i : Fin 2) : Finset U :=
  by classical exact (P.shrubVertices i).filter (fun v ↦ col v ≠ i)

noncomputable def farVertices (P : FineTreePartition T r ℓ col) (i : Fin 2) : Finset U :=
  by classical exact (P.shrubVertices i).filter (fun v ↦ col v = i)

theorem exists_unique_shrub_colour (P : FineTreePartition T r ℓ col)
    {C : Finset U} (hC : C ∈ P.shrubs) : ∃! i : Fin 2, C ∈ P.shrubsOfColour i := by
  classical
  obtain ⟨z, hz, hdz⟩ := P.has_attachment C hC
  refine ⟨col z, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    exact ⟨hC, fun u hu hdu ↦ P.attachment_colour C hC u hu z hz hdu hdz⟩
  · intro i hi
    exact ((Finset.mem_filter.mp hi).2 z hz hdz).symm

theorem shrubsOfColour_union (P : FineTreePartition T r ℓ col) :
    P.shrubsOfColour 0 ∪ P.shrubsOfColour 1 = P.shrubs := by
  classical
  ext C
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_filter.mp h).1
    · exact (Finset.mem_filter.mp h).1
  · intro hC
    obtain ⟨i, hi, _⟩ := P.exists_unique_shrub_colour hC
    fin_cases i
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ hi

theorem shrubsOfColour_disjoint (P : FineTreePartition T r ℓ col) :
    Disjoint (P.shrubsOfColour 0) (P.shrubsOfColour 1) := by
  classical
  apply Finset.disjoint_left.mpr
  intro C hzero hone
  have hC := (Finset.mem_filter.mp hzero).1
  obtain ⟨z, hz, hdz⟩ := P.has_attachment C hC
  have h0 := (Finset.mem_filter.mp hzero).2 z hz hdz
  have h1 := (Finset.mem_filter.mp hone).2 z hz hdz
  exact (by decide : (0 : Fin 2) ≠ 1) (h0.symm.trans h1)

theorem shrubVertices_disjoint (P : FineTreePartition T r ℓ col) :
    Disjoint (P.shrubVertices 0) (P.shrubVertices 1) := by
  classical
  apply Finset.disjoint_left.mpr
  intro u hzero hone
  obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp hzero
  obtain ⟨D, hD, huD⟩ := Finset.mem_biUnion.mp hone
  have hne : C ≠ D := by
    intro he
    exact Finset.disjoint_left.mp P.shrubsOfColour_disjoint hC (he.symm ▸ hD)
  exact Finset.disjoint_left.mp (P.disjoint_shrubs C (Finset.mem_filter.mp hC).1
    D (Finset.mem_filter.mp hD).1 hne) huC huD

theorem near_card_add_far_card (P : FineTreePartition T r ℓ col) (i : Fin 2) :
    (P.nearVertices i).card + (P.farVertices i).card = (P.shrubVertices i).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := P.shrubVertices i) (fun v ↦ col v = i)
  simpa only [nearVertices, farVertices, Nat.add_comm] using h

theorem shrubVertices_union (P : FineTreePartition T r ℓ col) :
    P.shrubVertices 0 ∪ P.shrubVertices 1 = P.shrubs.biUnion id := by
  classical
  unfold shrubVertices
  rw [← Finset.union_biUnion, P.shrubsOfColour_union]

theorem four_part_count (P : FineTreePartition T r ℓ col) :
    P.seeds.card + (P.nearVertices 0).card + (P.farVertices 0).card +
      (P.nearVertices 1).card + (P.farVertices 1).card = Fintype.card U := by
  classical
  have hdis : Disjoint P.seeds (P.shrubs.biUnion id) := by
    apply Finset.disjoint_left.mpr
    intro u hu hs
    obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp hs
    exact Finset.disjoint_left.mp (P.disjoint_seeds C hC) huC hu
  have hcover := Finset.card_union_of_disjoint hdis
  rw [P.cover, Finset.card_univ] at hcover
  have hsplit := Finset.card_union_of_disjoint P.shrubVertices_disjoint
  rw [P.shrubVertices_union] at hsplit
  have hzero := P.near_card_add_far_card 0
  have hone := P.near_card_add_far_card 1
  omega

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.exists_unique_shrub_colour
#print axioms Erdos547.FineTreePartition.shrubVertices_disjoint
#print axioms Erdos547.FineTreePartition.four_part_count
