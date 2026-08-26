/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourcePartialUsedCard
import ErdosProblems.Erdos547b.Lemma58SelectedOrientationReindex

/-!
# Exact preservation and endpoint usage for chosen owner batches

Appending a residual batch keeps the first batch's copies and orientations
literally. The new used set is exactly the union, including after canonical
selected-forest reindexing. These are set identities, not estimates.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoLemma58ChosenOwnerBatches

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58DynamicBatchAppend Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58SelectedOrientationReindex

variable {b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable (F : OrderedRootedForest b) (H : SimpleGraph V) (parent : Fin b → V)
variable (whole available : Fin 2 → Finset V)
variable (havailable : ∀ c, available c ⊆ whole c)
variable (hwhole : Disjoint (whole 0) (whole 1))
variable (s t : Finset (Fin b)) (hst : Disjoint s t)
variable (E₁ : ChosenPartialDynamicEmbedding F H parent available s)
variable (E₂ : ChosenPartialDynamicEmbedding F H parent (fun c => available c \ E₁.used c) t)

theorem ChosenPartialDynamicEmbedding.mem_used
    {F : OrderedRootedForest b} {H : SimpleGraph V} {parent : Fin b → V}
    {available : Fin 2 → Finset V} {s : Finset (Fin b)}
    (E : ChosenPartialDynamicEmbedding F H parent available s) (c : Fin 2) (v : V) :
    v ∈ E.used c ↔ ∃ i, ∃ hi : i ∈ s, ∃ a : Fin (F.size i),
      E.orient i ((F.isTree i).coloringTwoOfVert (F.root i) a) = c ∧
        E.state.forestCopy.componentCopy i hi a = v := by
  simp only [ChosenPartialDynamicEmbedding.used, PartialDynamicAttachedForestEmbedding.used,
    Finset.mem_biUnion, Finset.mem_univ, true_and, orientedCopyImage, Finset.mem_image,
    Finset.mem_filter, Subtype.exists]

theorem appendChosen_orient_left (i : Fin b) (hi : i ∈ s) :
    (appendChosen F H parent whole available havailable hwhole s t hst E₁ E₂).orient i =
      E₁.orient i := by
  simp only [appendChosen, pasteOrient, if_pos hi]

theorem appendChosen_orient_right (i : Fin b) (hi : i ∈ t) :
    (appendChosen F H parent whole available havailable hwhole s t hst E₁ E₂).orient i =
      E₂.orient i := by
  have hn : i ∉ s := fun hs => Finset.disjoint_left.mp hst hs hi
  simp only [appendChosen, pasteOrient, if_neg hn]

theorem appendChosen_copy_left (i : Fin b) (hi : i ∈ s) :
    (appendChosen F H parent whole available havailable hwhole s t hst E₁ E₂).state.forestCopy.componentCopy
      i (Finset.mem_union_left t hi) = E₁.state.forestCopy.componentCopy i hi := by
  simp only [appendChosen, appendPartial, reorientPartial, dif_pos hi]

theorem appendChosen_copy_right (i : Fin b) (hi : i ∈ t) :
    (appendChosen F H parent whole available havailable hwhole s t hst E₁ E₂).state.forestCopy.componentCopy
      i (Finset.mem_union_right s hi) = E₂.state.forestCopy.componentCopy i hi := by
  have hn : i ∉ s := fun hs => Finset.disjoint_left.mp hst hs hi
  simp only [appendChosen, appendPartial, reorientPartial, dif_neg hn]

theorem used_appendChosen (c : Fin 2) :
    (appendChosen F H parent whole available havailable hwhole s t hst E₁ E₂).used c =
      E₁.used c ∪ E₂.used c := by
  ext v
  rw [ChosenPartialDynamicEmbedding.mem_used, Finset.mem_union,
    E₁.mem_used, E₂.mem_used]
  constructor
  · rintro ⟨i, hi, a, hc, hv⟩
    rcases Finset.mem_union.mp hi with hs | ht
    · exact Or.inl ⟨i, hs, a,
        (by simpa only [appendChosen_orient_left F H parent whole available havailable hwhole s t hst E₁ E₂ i hs] using hc),
        (by simpa only [appendChosen_copy_left F H parent whole available havailable hwhole s t hst E₁ E₂ i hs] using hv)⟩
    · exact Or.inr ⟨i, ht, a,
        (by simpa only [appendChosen_orient_right F H parent whole available havailable hwhole s t hst E₁ E₂ i ht] using hc),
        (by simpa only [appendChosen_copy_right F H parent whole available havailable hwhole s t hst E₁ E₂ i ht] using hv)⟩
  · rintro (⟨i, hi, a, hc, hv⟩ | ⟨i, hi, a, hc, hv⟩)
    · exact ⟨i, Finset.mem_union_left t hi, a,
        (by simpa only [appendChosen_orient_left F H parent whole available havailable hwhole s t hst E₁ E₂ i hi] using hc),
        (by simpa only [appendChosen_copy_left F H parent whole available havailable hwhole s t hst E₁ E₂ i hi] using hv)⟩
    · exact ⟨i, Finset.mem_union_right s hi, a,
        (by simpa only [appendChosen_orient_right F H parent whole available havailable hwhole s t hst E₁ E₂ i hi] using hc),
        (by simpa only [appendChosen_copy_right F H parent whole available havailable hwhole s t hst E₁ E₂ i hi] using hv)⟩

theorem used_chosenPartialOfSelectedForest
    (localOrient : Fin s.card → Fin 2 ≃ Fin 2)
    (E : DynamicAttachedForestEmbedding (selectedForest F s) H
      (fun k => parent (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv s k))
      localOrient available) (c : Fin 2) :
    (chosenPartialOfSelectedForest F H parent available s localOrient E).used c = E.used c := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨i, hi, a, hc, hv⟩ :=
      (ChosenPartialDynamicEmbedding.mem_used _ c v).mp hv
    apply Finset.mem_biUnion.mpr
    refine ⟨selectedIndex s i hi, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨selectedVertex F s i hi a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simpa only [selectedVertex_coloring, chosenPartialOfSelectedForest,
        extendSelectedOrient, dif_pos hi] using hc
    · exact hv
  · change (E.used c).card ≤
      ((chosenPartialOfSelectedForest F H parent available s localOrient E).state.used c).card
    rw [E.card_used, PartialDynamicAttachedForestEmbedding.card_used, sideLoad_selectedForest]
    exact le_rfl

end Erdos547b.ZhaoLemma58ChosenOwnerBatches

#print axioms Erdos547b.ZhaoLemma58ChosenOwnerBatches.appendChosen_copy_left
#print axioms Erdos547b.ZhaoLemma58ChosenOwnerBatches.appendChosen_orient_left
#print axioms Erdos547b.ZhaoLemma58ChosenOwnerBatches.used_appendChosen
#print axioms Erdos547b.ZhaoLemma58ChosenOwnerBatches.used_chosenPartialOfSelectedForest
