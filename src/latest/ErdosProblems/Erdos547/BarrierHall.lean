import ErdosProblems.Erdos547.ExtremalBarrier
import Mathlib.Combinatorics.Hall.Finite

/-!
# Hall's condition between a barrier separator and its blocks
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

namespace SeparatesOn

theorem merge_remainder {A S U : Finset V} {F K : Finset (Finset V)}
    (h : SeparatesOn G A S F) (hUS : U ⊆ S) (hKF : K ⊆ F)
    (hclosed : ∀ C ∈ K, ∀ u ∈ C, ∀ v ∈ A \ U, G.Adj u v → v ∈ C)
    (hB : ((A \ U) \ K.biUnion id).Nonempty) :
    SeparatesOn G A U (insert ((A \ U) \ K.biUnion id) K) := by
  let B := (A \ U) \ K.biUnion id
  have hsub : K.biUnion id ⊆ A \ U := by
    intro u hu
    obtain ⟨C, hC, huC⟩ := Finset.mem_biUnion.mp hu
    have huAS := Finset.mem_sdiff.mp (h.part_subset (hKF hC) huC)
    exact Finset.mem_sdiff.mpr ⟨huAS.1, fun huU ↦ huAS.2 (hUS huU)⟩
  have hdisj (C : Finset V) (hC : C ∈ K) : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro u huB huC
    exact (Finset.mem_sdiff.mp huB).2 (Finset.mem_biUnion.mpr ⟨C, hC, huC⟩)
  refine ⟨hUS.trans h.separator_subset, ?_, ?_, ?_, ?_⟩
  · intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact hB
    · exact h.nonempty C (hKF hC)
  · intro C hC D hD hCD
    rcases Finset.mem_insert.mp hC with rfl | hC <;>
      rcases Finset.mem_insert.mp hD with rfl | hD
    · exact (hCD rfl).elim
    · exact hdisj D hD
    · exact (hdisj C hC).symm
    · exact h.disjoint (hKF hC) (hKF hD) hCD
  · rw [Finset.biUnion_insert]
    exact Finset.sdiff_union_of_subset hsub
  · intro C hC u hu v hv huv
    rcases Finset.mem_insert.mp hC with rfl | hC
    · apply Finset.mem_sdiff.mpr
      refine ⟨hv, ?_⟩
      intro hvK
      obtain ⟨D, hD, hvD⟩ := Finset.mem_biUnion.mp hvK
      have huD := hclosed D hD v hvD u (Finset.mem_sdiff.mp hu).1 huv.symm
      exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_biUnion.mpr ⟨D, hD, huD⟩)
    · exact hclosed C hC u hu v hv huv

end SeparatesOn

def adjacentBlocks (G : SimpleGraph V) (X : Finset V) (F : Finset (Finset V)) :
    Finset (Finset V) := by
  classical
  exact F.filter fun C ↦ ∃ x ∈ X, ∃ u ∈ C, G.Adj x u

namespace IsBarrier

variable [Finite V] {A S : Finset V} {F : Finset (Finset V)}

theorem hall_bound (h : IsBarrier G A S F) (X : Finset V) (hX : X ⊆ S) :
    X.card ≤ (adjacentBlocks G X F).card := by
  classical
  by_cases hne : X.Nonempty
  · let J := adjacentBlocks G X F
    let K := F \ J
    have hJF : J ⊆ F := Finset.filter_subset _ _
    have hKF : K ⊆ F := Finset.sdiff_subset
    have hclosed : ∀ C ∈ K, ∀ u ∈ C, ∀ v ∈ A \ (S \ X), G.Adj u v → v ∈ C := by
      intro C hC u hu v hv huv
      obtain ⟨hCF, hCJ⟩ := Finset.mem_sdiff.mp hC
      obtain ⟨hvA, hvSX⟩ := Finset.mem_sdiff.mp hv
      by_cases hvS : v ∈ S
      · have hvX : v ∈ X := by
          by_contra hvX
          exact hvSX (Finset.mem_sdiff.mpr ⟨hvS, hvX⟩)
        have hmem : C ∈ J := Finset.mem_filter.mpr ⟨hCF, v, hvX, u, hu, huv.symm⟩
        exact (hCJ hmem).elim
      · exact h.separates.closed C hCF u hu v (Finset.mem_sdiff.mpr ⟨hvA, hvS⟩) huv
    have hB : ((A \ (S \ X)) \ K.biUnion id).Nonempty := by
      obtain ⟨x, hx⟩ := hne
      refine ⟨x, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_sdiff.mpr ⟨h.separates.separator_subset (hX hx),
          fun hxSX ↦ (Finset.mem_sdiff.mp hxSX).2 hx⟩
      · intro hxK
        obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hxK
        exact Finset.disjoint_left.mp (h.separates.part_disjoint_separator (hKF hC)) hxC (hX hx)
    have href := h.separates.merge_remainder Finset.sdiff_subset hKF hclosed hB
    have hmax := h.maximal _ _ href
    have hoddF : oddParts F = F := by
      apply Finset.filter_eq_self.mpr
      exact fun C hC ↦ h.odd_part hC
    have hKodd : K ⊆ oddParts (insert ((A \ (S \ X)) \ K.biUnion id) K) := by
      intro C hC
      exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hC, h.odd_part (hKF hC)⟩
    have hKbound := Finset.card_le_card hKodd
    have hKcard : K.card = F.card - J.card := Finset.card_sdiff_of_subset hJF
    have hSX : (S \ X).card = S.card - X.card := Finset.card_sdiff_of_subset hX
    have hJcard := Finset.card_le_card hJF
    have hXcard := Finset.card_le_card hX
    rw [hoddF] at hmax
    change X.card ≤ J.card
    omega
  · have hXzero : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hXzero]

/-- Match every separator vertex to a different adjacent block. -/
theorem exists_block_assignment (h : IsBarrier G A S F) :
    ∃ f : ↥(S : Set V) → ↥(F : Set (Finset V)), Function.Injective f ∧
      ∀ x : (S : Set V), ∃ u ∈ (f x).val, G.Adj x.val u := by
  classical
  let blocks := fun x : (S : Set V) ↦ (Finset.univ : Finset (F : Set (Finset V))).filter
    fun C ↦ ∃ u ∈ C.val, G.Adj x.val u
  have hh : ∀ X : Finset (S : Set V), X.card ≤ (X.biUnion blocks).card := by
    intro X
    let Y : Finset V := X.image Subtype.val
    have hYS : Y ⊆ S := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
      exact x.property
    have hc : Y.card = X.card := Finset.card_image_of_injective X Subtype.val_injective
    have heq : (X.biUnion blocks).image Subtype.val = adjacentBlocks G Y F := by
      ext C
      simp only [Finset.mem_image, Finset.mem_biUnion, blocks, Finset.mem_filter,
        Finset.mem_univ, true_and, adjacentBlocks, Y]
      constructor
      · rintro ⟨D, ⟨x, hx, u, hu, hxu⟩, rfl⟩
        exact ⟨D.property, x.val, ⟨x, hx, rfl⟩, u, hu, hxu⟩
      · rintro ⟨hCF, x, ⟨y, hy, rfl⟩, u, hu, hyu⟩
        exact ⟨⟨C, hCF⟩, ⟨y, hy, u, hu, hyu⟩, rfl⟩
    have hi : (X.biUnion blocks).card = (adjacentBlocks G Y F).card := by
      rw [← heq, Finset.card_image_of_injective _ Subtype.val_injective]
    rw [hi, ← hc]
    exact h.hall_bound Y hYS
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' blocks).mp hh
  exact ⟨f, hf, fun x ↦ (Finset.mem_filter.mp (hmem x)).2⟩

end IsBarrier

end Erdos547.DPRS

#print axioms Erdos547.DPRS.IsBarrier.exists_block_assignment
