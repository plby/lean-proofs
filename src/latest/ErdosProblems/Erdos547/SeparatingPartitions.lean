import ErdosProblems.Erdos547.RootedPieces
import Mathlib.Combinatorics.SimpleGraph.Tutte

/-!
# Finite separating partitions

These partitions record a separator and the blocks left after deleting it.
Blocks need not initially be connected. This allows local refinement without
identifying successive quotient types of connected components.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

structure SeparatesOn (G : SimpleGraph V) (A S : Finset V) (F : Finset (Finset V)) : Prop where
  separator_subset : S ⊆ A
  nonempty : ∀ C ∈ F, C.Nonempty
  disjoint : (F : Set (Finset V)).Pairwise Disjoint
  cover : F.biUnion id = A \ S
  closed : ∀ C ∈ F, ∀ u ∈ C, ∀ v ∈ A \ S, G.Adj u v → v ∈ C

namespace SeparatesOn

variable {A S : Finset V} {F : Finset (Finset V)}

theorem part_subset (h : SeparatesOn G A S F) {C : Finset V} (hC : C ∈ F) : C ⊆ A \ S := by
  intro u hu
  rw [← h.cover]
  exact Finset.mem_biUnion.mpr ⟨C, hC, hu⟩

theorem part_subset_region (h : SeparatesOn G A S F) {C : Finset V} (hC : C ∈ F) : C ⊆ A :=
  fun _ hu ↦ (Finset.mem_sdiff.mp (h.part_subset hC hu)).1

theorem part_disjoint_separator (h : SeparatesOn G A S F) {C : Finset V} (hC : C ∈ F) :
    Disjoint C S := by
  apply Finset.disjoint_left.mpr
  intro u hu hS
  exact (Finset.mem_sdiff.mp (h.part_subset hC hu)).2 hS

theorem exists_part (h : SeparatesOn G A S F) {u : V} (hu : u ∈ A \ S) :
    ∃ C ∈ F, u ∈ C := by
  rw [← h.cover] at hu
  exact Finset.mem_biUnion.mp hu

theorem eq_of_mem_parts (h : SeparatesOn G A S F) {C D : Finset V}
    (hC : C ∈ F) (hD : D ∈ F) {u : V} (huC : u ∈ C) (huD : u ∈ D) : C = D := by
  by_contra hne
  exact Finset.disjoint_left.mp (h.disjoint hC hD hne) huC huD

theorem sum_card_parts (h : SeparatesOn G A S F) : ∑ C ∈ F, C.card = A.card - S.card := by
  rw [← Finset.card_biUnion (fun C hC D hD hne ↦ h.disjoint hC hD hne)]
  change (F.biUnion id).card = _
  rw [h.cover]
  exact Finset.card_sdiff_of_subset h.separator_subset

end SeparatesOn

def oddParts (F : Finset (Finset V)) : Finset (Finset V) := F.filter fun C ↦ Odd C.card

theorem SeparatesOn.odd_parts_iff {A S : Finset V} {F : Finset (Finset V)}
    (h : SeparatesOn G A S F) : Odd (oddParts F).card ↔ Odd (A.card - S.card) := by
  rw [← h.sum_card_parts]
  exact (Finset.odd_sum_iff_odd_card_odd (fun C : Finset V ↦ C.card)).symm

/-- A trivial partition whose separator is the entire region. -/
theorem separatesOn_empty (A : Finset V) : SeparatesOn G A A ∅ := by
  refine ⟨Subset.rfl, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · simp

/-- Connected components give a separating partition of any finite region
after any specified subset of vertices is deleted. -/
theorem exists_separating_partition_with_odd_count [Finite V] (G : SimpleGraph V)
    (A S : Finset V) (hS : S ⊆ A) :
    ∃ F, SeparatesOn G A S F ∧
      (oddParts F).card = (G.induce (↑(A \ S) : Set V)).oddComponents.ncard := by
  classical
  let := Fintype.ofFinite V
  let B : Set V := ↑(A \ S)
  let f := fun C : (G.induce B).ConnectedComponent ↦
    (Erdos547.inducedComponentSet G B C).toFinset
  let F := (Finset.univ : Finset (G.induce B).ConnectedComponent).image f
  have hsub (C : (G.induce B).ConnectedComponent) : f C ⊆ A \ S := by
    intro u hu
    exact Erdos547.inducedComponentSet_subset G B C (Set.mem_toFinset.mp hu)
  have hne (C : (G.induce B).ConnectedComponent) : (f C).Nonempty := by
    obtain ⟨u, hu⟩ := Erdos547.inducedComponentSet_nonempty G B C
    exact ⟨u, Set.mem_toFinset.mpr hu⟩
  have hf : Function.Injective f := by
    intro C D hCD
    obtain ⟨u, hu⟩ := hne C
    have huD : u ∈ f D := hCD ▸ hu
    obtain ⟨x, hx, hxu⟩ := Set.mem_toFinset.mp hu
    obtain ⟨y, hy, hyu⟩ := Set.mem_toFinset.mp huD
    have hxy : x = y := Subtype.ext (hxu.trans hyu.symm)
    exact ConnectedComponent.eq_of_common_vertex hx (hxy ▸ hy)
  have hcard (C : (G.induce B).ConnectedComponent) : (f C).card = C.supp.ncard := by
    change (Erdos547.inducedComponentSet G B C).toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card']
    exact Set.ncard_image_of_injective _ Subtype.val_injective
  refine ⟨F, ⟨hS, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro C hC
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hC
    exact hne D
  · intro C hC D hD hCD
    obtain ⟨C', _, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨D', _, rfl⟩ := Finset.mem_image.mp hD
    apply Finset.disjoint_left.mpr
    intro u huC huD
    obtain ⟨x, hx, hxu⟩ := Set.mem_toFinset.mp huC
    obtain ⟨y, hy, hyu⟩ := Set.mem_toFinset.mp huD
    have hxy : x = y := Subtype.ext (hxu.trans hyu.symm)
    have hcomp : C' = D' := ConnectedComponent.eq_of_common_vertex hx (hxy ▸ hy)
    exact hCD (congrArg f hcomp)
  · ext u
    constructor
    · intro hu
      obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp hu
      obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hC
      exact hsub D huC
    · intro hu
      let x : B := ⟨u, hu⟩
      let C := (G.induce B).connectedComponentMk x
      apply Finset.mem_biUnion.mpr
      refine ⟨f C, Finset.mem_image.mpr ⟨C, Finset.mem_univ _, rfl⟩, ?_⟩
      exact Set.mem_toFinset.mpr ⟨x, rfl, rfl⟩
  · intro C hC u hu v hv huv
    obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hC
    apply Set.mem_toFinset.mpr
    exact Erdos547.inducedComponentSet_closed G B D (Set.mem_toFinset.mp hu) hv huv
  · change (oddParts F).card = (G.induce B).oddComponents.ncard
    simp only [oddParts, F, Finset.filter_image, hcard, Finset.card_image_of_injective _ hf]
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext C
    simp

theorem exists_separating_partition [Finite V] (G : SimpleGraph V) (A S : Finset V)
    (hS : S ⊆ A) : ∃ F, SeparatesOn G A S F := by
  obtain ⟨F, hF, _⟩ := exists_separating_partition_with_odd_count G A S hS
  exact ⟨F, hF⟩

namespace SeparatesOn

variable {A S C U : Finset V} {F H : Finset (Finset V)}

theorem refinement_disjoint (h : SeparatesOn G A S F) (hC : C ∈ F)
    (h' : SeparatesOn G C U H) : Disjoint (F.erase C) H := by
  apply Finset.disjoint_left.mpr
  intro D hD hDH
  obtain ⟨u, hu⟩ := h'.nonempty D hDH
  have huC := h'.part_subset_region hDH hu
  exact Finset.disjoint_left.mp (h.disjoint (Finset.mem_of_mem_erase hD) hC
    (Finset.ne_of_mem_erase hD)) hu huC

/-- Replace one block by a further separating partition of that block. -/
theorem refine_part (h : SeparatesOn G A S F) (hC : C ∈ F)
    (h' : SeparatesOn G C U H) : SeparatesOn G A (S ∪ U) (F.erase C ∪ H) := by
  have hCU : U ⊆ C := h'.separator_subset
  have hCA : C ⊆ A := h.part_subset_region hC
  have hCS : Disjoint C S := h.part_disjoint_separator hC
  have hkeep : ∀ D ∈ F.erase C, Disjoint D C := fun D hD ↦
    h.disjoint (Finset.mem_of_mem_erase hD) hC (Finset.ne_of_mem_erase hD)
  refine ⟨Finset.union_subset h.separator_subset (hCU.trans hCA), ?_, ?_, ?_, ?_⟩
  · intro D hD
    rcases Finset.mem_union.mp hD with hD | hD
    · exact h.nonempty D (Finset.mem_of_mem_erase hD)
    · exact h'.nonempty D hD
  · intro D hD E hE hDE
    rcases Finset.mem_union.mp hD with hD | hD <;>
      rcases Finset.mem_union.mp hE with hE | hE
    · exact h.disjoint (Finset.mem_of_mem_erase hD) (Finset.mem_of_mem_erase hE) hDE
    · exact (hkeep D hD).mono_right (h'.part_subset_region hE)
    · exact ((hkeep E hE).mono_right (h'.part_subset_region hD)).symm
    · exact h'.disjoint hD hE hDE
  · ext u
    constructor
    · intro hu
      obtain ⟨D, hD, huD⟩ := Finset.mem_biUnion.mp hu
      rcases Finset.mem_union.mp hD with hD | hD
      · have huAS := Finset.mem_sdiff.mp (h.part_subset (Finset.mem_of_mem_erase hD) huD)
        refine Finset.mem_sdiff.mpr ⟨huAS.1, ?_⟩
        intro husu
        rcases Finset.mem_union.mp husu with huS | huU
        · exact huAS.2 huS
        · exact Finset.disjoint_left.mp (hkeep D hD) huD (hCU huU)
      · have huCU := Finset.mem_sdiff.mp (h'.part_subset hD huD)
        refine Finset.mem_sdiff.mpr ⟨hCA huCU.1, ?_⟩
        intro husu
        rcases Finset.mem_union.mp husu with huS | huU
        · exact Finset.disjoint_left.mp hCS huCU.1 huS
        · exact huCU.2 huU
    · intro hu
      obtain ⟨huA, huSU⟩ := Finset.mem_sdiff.mp hu
      have huS : u ∉ S := fun huS ↦ huSU (Finset.mem_union_left _ huS)
      have huU : u ∉ U := fun huU ↦ huSU (Finset.mem_union_right _ huU)
      by_cases huC : u ∈ C
      · obtain ⟨D, hD, huD⟩ := h'.exists_part (Finset.mem_sdiff.mpr ⟨huC, huU⟩)
        exact Finset.mem_biUnion.mpr ⟨D, Finset.mem_union_right _ hD, huD⟩
      · obtain ⟨D, hD, huD⟩ := h.exists_part (Finset.mem_sdiff.mpr ⟨huA, huS⟩)
        have hDC : D ≠ C := fun hDC ↦ huC (hDC ▸ huD)
        exact Finset.mem_biUnion.mpr ⟨D,
          Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hDC, hD⟩), huD⟩
  · intro D hD u hu v hv huv
    obtain ⟨hvA, hvSU⟩ := Finset.mem_sdiff.mp hv
    have hvS : v ∉ S := fun hvS ↦ hvSU (Finset.mem_union_left _ hvS)
    have hvU : v ∉ U := fun hvU ↦ hvSU (Finset.mem_union_right _ hvU)
    rcases Finset.mem_union.mp hD with hD | hD
    · exact h.closed D (Finset.mem_of_mem_erase hD) u hu v
        (Finset.mem_sdiff.mpr ⟨hvA, hvS⟩) huv
    · have huC := h'.part_subset_region hD hu
      have hvC := h.closed C hC u huC v (Finset.mem_sdiff.mpr ⟨hvA, hvS⟩) huv
      exact h'.closed D hD u hu v (Finset.mem_sdiff.mpr ⟨hvC, hvU⟩) huv

theorem refined_separator_card (h : SeparatesOn G A S F) (hC : C ∈ F)
    (h' : SeparatesOn G C U H) : (S ∪ U).card = S.card + U.card :=
  Finset.card_union_of_disjoint ((h.part_disjoint_separator hC).symm.mono_right h'.separator_subset)

theorem refined_odd_card (h : SeparatesOn G A S F) (hC : C ∈ F)
    (h' : SeparatesOn G C U H) :
    (oddParts (F.erase C ∪ H)).card + (if Odd C.card then 1 else 0) =
      (oddParts F).card + (oddParts H).card := by
  classical
  have heq : oddParts (F.erase C ∪ H) = (oddParts F).erase C ∪ oddParts H := by
    ext D
    simp only [oddParts, Finset.mem_filter, Finset.mem_union, Finset.mem_erase]
    tauto
  rw [heq, Finset.card_union_of_disjoint]
  · by_cases ho : Odd C.card
    · have hmem : C ∈ oddParts F := Finset.mem_filter.mpr ⟨hC, ho⟩
      rw [if_pos ho]
      have hcard := Finset.card_erase_add_one hmem
      omega
    · have hmem : C ∉ oddParts F := by simp [oddParts, ho]
      simp [if_neg ho, Finset.erase_eq_of_notMem hmem]
  · apply (h.refinement_disjoint hC h').mono
    · intro D hD
      obtain ⟨hne, hDF⟩ := Finset.mem_erase.mp hD
      exact Finset.mem_erase.mpr ⟨hne, (Finset.mem_filter.mp hDF).1⟩
    · exact Finset.filter_subset _ _

end SeparatesOn

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_separating_partition
#print axioms Erdos547.DPRS.SeparatesOn.refine_part
