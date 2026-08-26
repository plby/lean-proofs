/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58ChosenOwnerBatches
import ErdosProblems.Erdos547b.SourceDynamicUsedCard

/-!
# Exact occupied counts of a chosen partial owner prefix

The actual two-side used count is the source order already copied. A
disjoint current batch is charged only once. Adding permanent deletions
therefore gives the actual occupied-plus-batch bound used by Part 3.
-/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoLemma58DynamicBatchAppend

open Finset SimpleGraph Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest

variable {b : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
variable {F : OrderedRootedForest b} {H : SimpleGraph V}
variable {parent : Fin b → V} {orient : Fin b → Fin 2 ≃ Fin 2}
variable {available : Fin 2 → Finset V} {selected : Finset (Fin b)}

theorem PartialDynamicAttachedForestEmbedding.card_used
    (E : PartialDynamicAttachedForestEmbedding F H parent orient available selected) (c : Fin 2) :
    (E.used c).card = ∑ i ∈ selected, orientedClassSize F orient i c := by
  unfold PartialDynamicAttachedForestEmbedding.used
  rw [Finset.card_biUnion]
  · calc
      (∑ i : {i // i ∈ selected},
        #(orientedCopyImage (F.tree i.1) (F.isTree i.1) (F.root i.1) (orient i.1) H
          (E.forestCopy.componentCopy i.1 i.2) c)) =
          ∑ i : {i // i ∈ selected}, orientedClassSize F orient i.1 c := by
        apply Finset.sum_congr rfl
        intro i _
        exact card_orientedCopyImage (F.tree i.1) (F.isTree i.1) (F.root i.1)
          (orient i.1) H (E.forestCopy.componentCopy i.1 i.2) c
      _ = _ := Finset.sum_attach selected (fun i => orientedClassSize F orient i c)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hv
    obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hw
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    exact Set.disjoint_left.mp (E.forestCopy.disjoint_ranges i.1 i.2 j.1 j.2 hne) ⟨a, ha⟩ ⟨d, hd⟩

theorem PartialDynamicAttachedForestEmbedding.card_used_zero_add_one
    (E : PartialDynamicAttachedForestEmbedding F H parent orient available selected) :
    (E.used 0).card + (E.used 1).card = ∑ i ∈ selected, F.size i := by
  rw [E.card_used 0, E.card_used 1, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => orientedClassSize_zero_add_one F orient i)

theorem PartialDynamicAttachedForestEmbedding.card_used_add_batch_le_order
    (E : PartialDynamicAttachedForestEmbedding F H parent orient available selected)
    (batch : Finset (Fin b)) (hdisjoint : Disjoint selected batch) :
    (E.used 0).card + (E.used 1).card + (∑ i ∈ batch, F.size i) ≤ F.order := by
  rw [E.card_used_zero_add_one, ← Finset.sum_union hdisjoint]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

omit [Fintype V] in
private theorem occupied_count_identity (whole deleted used : Finset V) (N : ℕ)
    (hwhole : whole.card = N) (hdeleted : deleted ⊆ whole) (hused : used ⊆ whole \ deleted) :
    ((whole \ deleted) \ used).card + used.card + deleted.card = N := by
  rw [Finset.card_sdiff_add_card_eq_card hused,
    Finset.card_sdiff_add_card_eq_card hdeleted, hwhole]

/-- The current graph prefix and source disjointness supply the effective
Part-3 mass bound, with permanent deletions charged separately. -/
theorem PartialDynamicAttachedForestEmbedding.occupied_add_batch_le
    (whole deleted : Fin 2 → Finset V) (N : ℕ)
    (hwhole : ∀ c, (whole c).card = N) (hdeleted : ∀ c, deleted c ⊆ whole c)
    (E : PartialDynamicAttachedForestEmbedding F H parent orient (fun c => whole c \ deleted c) selected)
    (batch : Finset (Fin b)) (hdisjoint : Disjoint selected batch) :
    ((N : ℝ) - ((whole 0 \ deleted 0) \ E.used 0).card) +
      ((N : ℝ) - ((whole 1 \ deleted 1) \ E.used 1).card) + (∑ i ∈ batch, F.size i : ℕ) ≤
        (deleted 0).card + (deleted 1).card + (F.order : ℝ) := by
  have hcount (c : Fin 2) : (((whole c \ deleted c) \ E.used c).card : ℝ) +
      (E.used c).card + (deleted c).card = N := by
    exact_mod_cast occupied_count_identity (whole c) (deleted c) (E.used c) N
      (hwhole c) (hdeleted c) (E.used_subset c)
  have hmass : ((E.used 0).card : ℝ) + (E.used 1).card + (∑ i ∈ batch, F.size i : ℕ) ≤ F.order := by
    exact_mod_cast E.card_used_add_batch_le_order batch hdisjoint
  linarith only [hcount 0, hcount 1, hmass]

end Erdos547b.ZhaoLemma58DynamicBatchAppend

#print axioms Erdos547b.ZhaoLemma58DynamicBatchAppend.PartialDynamicAttachedForestEmbedding.card_used
#print axioms Erdos547b.ZhaoLemma58DynamicBatchAppend.PartialDynamicAttachedForestEmbedding.card_used_zero_add_one
#print axioms Erdos547b.ZhaoLemma58DynamicBatchAppend.PartialDynamicAttachedForestEmbedding.card_used_add_batch_le_order
#print axioms Erdos547b.ZhaoLemma58DynamicBatchAppend.PartialDynamicAttachedForestEmbedding.occupied_add_batch_le
