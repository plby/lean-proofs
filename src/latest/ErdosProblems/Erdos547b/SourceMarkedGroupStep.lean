/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceMarkedAvailableSets

/-!
# Actual occupied-set extension for one marked branch

The private pair, all three available sets, the attached copy and its
marked A-reservoir degrees are constructed from the actual used set.
No old image is changed, and the returned copy avoids every old image.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMarkedGroupStep

open Finset SimpleGraph
open Erdos547b.ZhaoSourceMarkedAvailableSets Erdos547b.ZhaoSourceMarkedTripleEmbedding
open Erdos547b.ZhaoMarkedTripleLoads Erdos547b.ZhaoSourceParentCleanup
open Erdos547b.ZhaoSourceEmbeddingHost Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceFreshChunkBounds
open Erdos547b.ZhaoStability Erdos547b.ZhaoEvenReducedPadding

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W)

theorem exists_groupStep (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (C : Index W) (X Y : Fin 4 → Index W)
    (hCA : (reduced W).Adj C Q.A)
    (hCX : ∀ i, (reduced W).Adj C (X i))
    (hYX : ∀ i, (reduced W).Adj (Y i) (X i))
    (hCdisjoint : ∀ i, Disjoint (whole W C) (whole W (X i) ∪ whole W (Y i)))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (whole W (X i) ∪ whole W (Y i))
      (whole W (X j) ∪ whole W (Y j)))
    (used : Finset (Fin hostN)) (z : Fin hostN)
    (hparent : (1 - 2 * (eta α : ℝ) - (gamma α : ℝ)) * W.clusterSize ≤
      (((whole W C).filter ((embeddingHost W).Adj z)).card : ℝ))
    (husedC : ((used ∩ whole W C).card : ℝ) ≤
      (1 - 2 * (eta α : ℝ) - 3 * (gamma α : ℝ)) * W.clusterSize)
    (husedPairs : (used ∩ privatePairUnion W X Y).card ≤ 3 * W.clusterSize)
    {A : Type*} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A) (special : Finset A)
    (hspecial : ∀ a ∈ special, hT.coloringTwoOfVert root a = 0)
    (hsmall : Fintype.card A ≤ freshBranchBound α W.clusterSize) :
    ∃ (i : Fin 4) (f : T.Copy (embeddingHost W)),
      (embeddingHost W).Adj z (f root) ∧
      (∀ a, f a ∉ used) ∧
      (∀ a ∈ insert root special,
        f a ∈ whole W C \ badToward W Q (Sum.inl C) 0 ∧
        ((densityCutoff α : ℝ) - (epsilon α : ℝ)) * (sourceQuota W : ℝ) ≤
          ((Q.A₀.filter ((embeddingHost W).Adj (f a))).card : ℝ)) ∧
      (∀ a, a ≠ root → a ∉ special →
        f a ∈ if hT.coloringTwoOfVert root a = 0 then whole W (Y i) else whole W (X i)) ∧
      ((Finset.univ.image f) ∩ whole W C).card ≤ 1 + special.card ∧
      Finset.univ.image f ⊆ whole W C ∪ whole W (X i) ∪ whole W (Y i) := by
  let C' := intermediateAvailable W Q C used z
  have hC' : C' ⊆ whole W C := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).1
  have hattach : ∀ v ∈ C', (embeddingHost W).Adj z v := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
  have hclean : ∀ v ∈ C', v ∈ whole W C \ badToward W Q (Sum.inl C) 0 ∧ v ∉ used := by
    intro v hv
    have hn := (Finset.mem_sdiff.mp hv).2
    exact ⟨Finset.mem_sdiff.mpr ⟨hC' hv, fun hb => hn (Finset.mem_union_right _ hb)⟩,
      fun hu => hn (Finset.mem_union_left _ hu)⟩
  have hCLarge := intermediateAvailable_card_ge W Q hα hα1 C used z hparent husedC
  obtain ⟨i, hXlarge, hYlarge⟩ := exists_available_private_pair W hα hα1 X Y used hdisjoint husedPairs
  obtain ⟨f, hfattach, hfroot, hfspecial, hfother⟩ := exists_markedBranchCopy W hα hα1
    C (X i) (Y i) (hCX i) (hYX i) C' (whole W (X i) \ used) (whole W (Y i) \ used)
    hC' Finset.sdiff_subset Finset.sdiff_subset hCLarge hXlarge hYlarge
    T hT root special hspecial hsmall z hattach
  have hmarked : ∀ a ∈ insert root special, f a ∈ C' := by
    intro a ha
    rcases Finset.mem_insert.mp ha with ha | ha
    · simpa only [ha] using hfroot
    · exact hfspecial a ha
  have hotherUsed : ∀ a, a ≠ root → a ∉ special →
      f a ∈ (whole W (X i) \ used) ∪ (whole W (Y i) \ used) := by
    intro a har ha
    have hm := hfother a har ha
    split_ifs at hm
    · exact Finset.mem_union_right _ hm
    · exact Finset.mem_union_left _ hm
  have hother : ∀ a, a ≠ root → a ∉ special → f a ∈ whole W (X i) ∪ whole W (Y i) := by
    intro a har ha
    rcases Finset.mem_union.mp (hotherUsed a har ha) with hx | hy
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hy).1
  have hfresh : ∀ a, f a ∉ used := by
    intro a
    by_cases ha : a ∈ insert root special
    · exact (hclean (f a) (hmarked a ha)).2
    have han : a ≠ root ∧ a ∉ special := by simpa only [Finset.mem_insert, not_or] using ha
    rcases Finset.mem_union.mp (hotherUsed a han.1 han.2) with hx | hy
    · exact (Finset.mem_sdiff.mp hx).2
    · exact (Finset.mem_sdiff.mp hy).2
  have hrootC : f root ∈ whole W C := hC' hfroot
  have hspecialC : ∀ a ∈ special, f a ∈ whole W C := fun a ha => hC' (hfspecial a ha)
  refine ⟨i, f, hfattach, hfresh, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have hc := (hclean (f a) (hmarked a ha)).1
    refine ⟨hc, ?_⟩
    exact degree_into_reservoir_of_not_mem_badToward W Q (Sum.inl C) 0 (f a)
      (Finset.mem_sdiff.mp hc).1 (Finset.mem_sdiff.mp hc).2
      (by simpa [rootCluster] using hCA)
  · intro a har ha
    have h := hfother a har ha
    split_ifs at h ⊢ with hc
    · exact (Finset.mem_sdiff.mp h).1
    · exact (Finset.mem_sdiff.mp h).1
  · exact intermediate_load_bound f root special (whole W C) (whole W (X i)) (whole W (Y i))
      hrootC hspecialC hother (Finset.disjoint_union_right.mp (hCdisjoint i)).1
      (Finset.disjoint_union_right.mp (hCdisjoint i)).2
  · exact image_subset_three_sets f root special (whole W C) (whole W (X i)) (whole W (Y i))
      hrootC hspecialC hother

end Erdos547b.ZhaoSourceMarkedGroupStep

#print axioms Erdos547b.ZhaoSourceMarkedGroupStep.exists_groupStep
