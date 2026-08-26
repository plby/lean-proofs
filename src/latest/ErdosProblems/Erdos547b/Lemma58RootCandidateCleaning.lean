/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalCanonicalCleaning
import ErdosProblems.Erdos547b.Lemma58RootSkeleton

/-!
# Target-relative cleaning of the Lemma-5.8 root reservoirs

Each component root must be typical toward a finite family of actual target
reservoirs: the matching endpoints used by its own branches, the endpoint
containing its internal cut parent, and (for root/root cut edges) the opposite
root reservoir.  This file packages the common finite-union cleaning step.

The construction is deliberately generic in the target index.  Claim 6.15
and Claim 6.16 can therefore use their different matching-edge families
without changing the graph argument.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoLemma58RootCandidateCleaning

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest
open Erdos547b.TreePartition
open Erdos547b.ZhaoLemma58RootSkeleton

universe u w x

/-- Union of target-relative low-degree vertices for the actual targets
required by one root. -/
noncomputable def rootTargetBad
    {B : Type u} [Fintype B] [DecidableEq B]
    {R : Type x} {Target : Type w} [Fintype Target] [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : R → Finset B)
    (targets : R → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (q : R) : Finset B :=
  (targets q).biUnion fun t ↦
    targetLowDegreeVertices G rho (rootWhole q) (targetWhole t)
      (rootRaw q) (targetRaw t)

/-- Literal cleaned candidate reservoir for one root. -/
noncomputable def rootCandidate
    {B : Type u} [Fintype B] [DecidableEq B]
    {R : Type x} {Target : Type w} [Fintype Target] [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : R → Finset B)
    (targets : R → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (q : R) : Finset B :=
  rootRaw q \ rootTargetBad G rho rootWhole rootRaw targets
    targetWhole targetRaw q

theorem rootCandidate_subset_raw
    {B : Type u} [Fintype B] [DecidableEq B]
    {R : Type x} {Target : Type w} [Fintype Target] [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : R → Finset B)
    (targets : R → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (q : R) :
    rootCandidate G rho rootWhole rootRaw targets targetWhole targetRaw q ⊆
      rootRaw q :=
  Finset.sdiff_subset

/-- Standard regularity union bound for one root's complete target list. -/
theorem card_rootTargetBad_le
    {B : Type u} [Fintype B] [DecidableEq B]
    {R : Type x} {Target : Type w} [Fintype Target] [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : R → Finset B)
    (targets : R → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (q : R)
    (huniform : ∀ t ∈ targets q,
      G.IsUniform rho (rootWhole q) (targetWhole t))
    (hrootSub : rootRaw q ⊆ rootWhole q)
    (htargetSub : ∀ t ∈ targets q, targetRaw t ⊆ targetWhole t)
    (hrootLarge : rho * #(rootWhole q) ≤ #(rootRaw q))
    (htargetLarge : ∀ t ∈ targets q,
      rho * #(targetWhole t) ≤ #(targetRaw t)) :
    (#(rootTargetBad G rho rootWhole rootRaw targets targetWhole targetRaw q) : ℝ)
      ≤ (#(targets q) : ℝ) * (rho * #(rootWhole q)) := by
  have hcardNat :
      #(rootTargetBad G rho rootWhole rootRaw targets targetWhole targetRaw q) ≤
        ∑ t ∈ targets q,
          #(targetLowDegreeVertices G rho (rootWhole q) (targetWhole t)
            (rootRaw q) (targetRaw t)) := by
    exact Finset.card_biUnion_le
  calc
    (#(rootTargetBad G rho rootWhole rootRaw targets targetWhole targetRaw q) : ℝ)
        ≤ ∑ t ∈ targets q,
          (#(targetLowDegreeVertices G rho (rootWhole q) (targetWhole t)
            (rootRaw q) (targetRaw t)) : ℝ) := by
      exact_mod_cast hcardNat
    _ ≤ ∑ _t ∈ targets q, rho * #(rootWhole q) := by
      apply Finset.sum_le_sum
      intro t ht
      exact card_targetLowDegreeVertices_le G (huniform t ht) hrootSub
        (htargetSub t ht) hrootLarge (htargetLarge t ht)
    _ = (#(targets q) : ℝ) * (rho * #(rootWhole q)) := by simp

/-- A direct natural loss budget yields the cardinality needed by the online
root selector. -/
theorem root_count_le_card_rootCandidate
    {B : Type u} [Fintype B] [DecidableEq B]
    {R : Type x} {Target : Type w} [Fintype Target] [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : R → Finset B)
    (targets : R → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (q : R) (rootCount loss : ℕ)
    (hbad : #(rootTargetBad G rho rootWhole rootRaw targets
      targetWhole targetRaw q) ≤ loss)
    (hbudget : rootCount + loss ≤ #(rootRaw q)) :
    rootCount ≤ #(rootCandidate G rho rootWhole rootRaw targets
      targetWhole targetRaw q) := by
  have hsplit := Finset.card_sdiff_add_card_inter (rootRaw q)
    (rootTargetBad G rho rootWhole rootRaw targets targetWhole targetRaw q)
  have hinter : #((rootRaw q) ∩ rootTargetBad G rho rootWhole rootRaw targets
      targetWhole targetRaw q) ≤ loss :=
    (Finset.card_le_card Finset.inter_subset_right).trans hbad
  change rootCount ≤ #((rootRaw q) \ rootTargetBad G rho rootWhole rootRaw
    targets targetWhole targetRaw q)
  omega

/-- Membership in the cleaned root reservoir gives the exact real degree
bound toward every listed raw target. -/
theorem rootCandidate_target_degree
    {B : Type u} [Fintype B] [DecidableEq B]
    {R : Type x} {Target : Type w} [Fintype Target] [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : R → Finset B)
    (targets : R → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (q : R) (z : B)
    (hz : z ∈ rootCandidate G rho rootWhole rootRaw targets
      targetWhole targetRaw q)
    (t : Target) (ht : t ∈ targets q) :
    (G.edgeDensity (rootWhole q) (targetWhole t) - rho) * #(targetRaw t) ≤
      (#((targetRaw t).filter (G.Adj z)) : ℝ) := by
  have hzRaw := (Finset.mem_sdiff.mp hz).1
  have hzGood : z ∉ targetLowDegreeVertices G rho
      (rootWhole q) (targetWhole t) (rootRaw q) (targetRaw t) := by
    intro hzLow
    exact (Finset.mem_sdiff.mp hz).2 (Finset.mem_biUnion.mpr
      ⟨t, ht, hzLow⟩)
  exact target_degree_ge_of_not_mem_lowDegree G rho (rootWhole q)
    (targetWhole t) (rootRaw q) (targetRaw t) z hzRaw hzGood

/-- Deleting a target-side set of size `removed` loses at most `removed`
neighbours.  This is the arithmetic used for root/root skeleton links after
both root reservoirs have been cleaned. -/
theorem rootCount_le_neighbors_rootCandidate
    {B : Type u} [Fintype B] [DecidableEq B]
    {R : Type x} {Target : Type w} [Fintype Target] [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : R → Finset B)
    (targets : R → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (q q' : R) (z : B) (t : Target)
    (ht : t ∈ targets q)
    (hz : z ∈ rootCandidate G rho rootWhole rootRaw targets
      targetWhole targetRaw q)
    (htarget : targetRaw t = rootRaw q')
    (rootCount removed : ℕ)
    (hremoved : #(rootTargetBad G rho rootWhole rootRaw targets
      targetWhole targetRaw q') ≤ removed)
    (hdegree : (rootCount : ℝ) + removed ≤
      (G.edgeDensity (rootWhole q) (targetWhole t) - rho) * #(targetRaw t)) :
    rootCount ≤ #((rootCandidate G rho rootWhole rootRaw targets
      targetWhole targetRaw q').filter (G.Adj z)) := by
  have hrawReal := rootCandidate_target_degree G rho rootWhole rootRaw targets
    targetWhole targetRaw q z hz t ht
  have hrawNat : rootCount + removed ≤ #((targetRaw t).filter (G.Adj z)) := by
    exact_mod_cast hdegree.trans hrawReal
  let bad' := rootTargetBad G rho rootWhole rootRaw targets
    targetWhole targetRaw q'
  have hsub :
      ((targetRaw t).filter (G.Adj z)) \ bad' ⊆
        (rootCandidate G rho rootWhole rootRaw targets
          targetWhole targetRaw q').filter (G.Adj z) := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    have hxRawAdj := Finset.mem_filter.mp hx'.1
    apply Finset.mem_filter.mpr
    refine ⟨?_, hxRawAdj.2⟩
    rw [rootCandidate]
    exact Finset.mem_sdiff.mpr
      ⟨by simpa only [← htarget] using hxRawAdj.1, hx'.2⟩
  have hsplit := Finset.card_sdiff_add_card_inter
    ((targetRaw t).filter (G.Adj z)) bad'
  have hinter : #(((targetRaw t).filter (G.Adj z)) ∩ bad') ≤ removed :=
    (Finset.card_le_card Finset.inter_subset_right).trans hremoved
  have hlive : rootCount ≤
      #(((targetRaw t).filter (G.Adj z)) \ bad') := by omega
  exact hlive.trans (Finset.card_le_card hsub)

/-- The generic cleaning arithmetic directly supplies the online root
skeleton when every root/root cut link names the opposite raw root
reservoir among the parent's target list. -/
theorem exists_rootSkeletonEmbedding_of_targetCleaning
    {V : Type w} [Fintype V] [DecidableEq V]
    {Tgraph : SimpleGraph V} [DecidableRel Tgraph.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition Tgraph globalRoot small)
    {B : Type u} [Fintype B] [DecidableEq B]
    {Target : Type x} [Fintype Target] [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : Fin P.numParts → Finset B)
    (targets : Fin P.numParts → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (loss : Fin P.numParts → ℕ)
    (hbad : ∀ q, #(rootTargetBad G rho rootWhole rootRaw targets
      targetWhole targetRaw q) ≤ loss q)
    (hbudget : ∀ q, P.numParts + loss q ≤ #(rootRaw q))
    (hrootTarget : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj)),
      ∃ t ∈ targets (P.parentPart j hj), targetRaw t = rootRaw j)
    (hrootDegree : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj))
      (t : Target) (ht : t ∈ targets (P.parentPart j hj))
      (htarget : targetRaw t = rootRaw j),
      (P.numParts : ℝ) + loss j ≤
        (G.edgeDensity (rootWhole (P.parentPart j hj)) (targetWhole t) - rho) *
          #(targetRaw t)) :
    Nonempty (RootSkeletonEmbedding P G
      (rootCandidate G rho rootWhole rootRaw targets targetWhole targetRaw)) := by
  apply exists_rootSkeletonEmbedding P G
    (rootCandidate G rho rootWhole rootRaw targets targetWhole targetRaw)
  · intro q
    exact root_count_le_card_rootCandidate G rho rootWhole rootRaw targets
      targetWhole targetRaw q P.numParts (loss q) (hbad q) (hbudget q)
  · intro j hj hroot z hz
    obtain ⟨t, ht, htarget⟩ := hrootTarget j hj hroot
    exact rootCount_le_neighbors_rootCandidate G rho rootWhole rootRaw targets
      targetWhole targetRaw (P.parentPart j hj) j z t ht hz htarget
      P.numParts (loss j) (hbad j)
      (hrootDegree j hj hroot t ht htarget)

/-- Sharper root-link form of the target-cleaning constructor.  The target
and its density estimate are supplied together, so the caller need not prove
the estimate for unrelated targets whose raw sets happen to be equal. -/
theorem exists_rootSkeletonEmbedding_of_targetCleaningWithLinks
    {V : Type w} [Fintype V] [DecidableEq V]
    {Tgraph : SimpleGraph V} [DecidableRel Tgraph.Adj]
    {globalRoot : V} {small : ℕ}
    (P : ZhaoForestPartition Tgraph globalRoot small)
    {B : Type u} [Fintype B] [DecidableEq B]
    {Target : Type x} [Fintype Target] [DecidableEq Target]
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (rho : ℝ)
    (rootWhole rootRaw : Fin P.numParts → Finset B)
    (targets : Fin P.numParts → Finset Target)
    (targetWhole targetRaw : Target → Finset B)
    (loss : Fin P.numParts → ℕ)
    (hbad : ∀ q, #(rootTargetBad G rho rootWhole rootRaw targets
      targetWhole targetRaw q) ≤ loss q)
    (hbudget : ∀ q, P.numParts + loss q ≤ #(rootRaw q))
    (hrootLink : ∀ j (hj : j.val ≠ 0)
      (hroot : P.parent j hj = P.roots (P.parentPart j hj)),
      ∃ t ∈ targets (P.parentPart j hj),
        targetRaw t = rootRaw j ∧
        (P.numParts : ℝ) + loss j ≤
          (G.edgeDensity (rootWhole (P.parentPart j hj)) (targetWhole t) -
            rho) * #(targetRaw t)) :
    Nonempty (RootSkeletonEmbedding P G
      (rootCandidate G rho rootWhole rootRaw targets targetWhole targetRaw)) := by
  apply exists_rootSkeletonEmbedding P G
    (rootCandidate G rho rootWhole rootRaw targets targetWhole targetRaw)
  · intro q
    exact root_count_le_card_rootCandidate G rho rootWhole rootRaw targets
      targetWhole targetRaw q P.numParts (loss q) (hbad q) (hbudget q)
  · intro j hj hroot z hz
    obtain ⟨t, ht, htarget, hdegree⟩ := hrootLink j hj hroot
    exact rootCount_le_neighbors_rootCandidate G rho rootWhole rootRaw targets
      targetWhole targetRaw (P.parentPart j hj) j z t ht hz htarget
      P.numParts (loss j) (hbad j) hdegree

end Erdos547b.ZhaoLemma58RootCandidateCleaning

#print axioms Erdos547b.ZhaoLemma58RootCandidateCleaning.card_rootTargetBad_le
#print axioms Erdos547b.ZhaoLemma58RootCandidateCleaning.rootCount_le_neighbors_rootCandidate
#print axioms Erdos547b.ZhaoLemma58RootCandidateCleaning.exists_rootSkeletonEmbedding_of_targetCleaning
#print axioms Erdos547b.ZhaoLemma58RootCandidateCleaning.exists_rootSkeletonEmbedding_of_targetCleaningWithLinks
