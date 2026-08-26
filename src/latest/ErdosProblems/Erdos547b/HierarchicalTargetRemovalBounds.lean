/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.HierarchicalTargetCleaning

/-!
# Aggregate bounds for target-relative hierarchy cleaning

The target cleaner deliberately records its exceptional sets literally.
This module supplies the regularity estimate which turns those literal
unions into the aggregate removal budget used by the Section 6 allocator.
-/

open scoped SimpleGraph BigOperators

noncomputable section

namespace Erdos547b.ZhaoLemma59HierarchicalTargetRemovalBounds

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoLemma59Hierarchical
open Erdos547b.ZhaoLemma59HierarchicalRegular
open Erdos547b.ZhaoLemma59HierarchicalCanonical
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning
open Erdos547b.ZhaoLemma59HierarchicalCanonical.HierarchicalSegmentForest
open Erdos547b.ZhaoLemma59HierarchicalTargetCleaning.HierarchicalSegmentForest

universe u

namespace HierarchicalSegmentForest

variable {r s c : ℕ} {B : Type u} {RootGroup : Type*}

/-- The union removed from one source coordinate costs at most the sum of
the regularity errors for its hierarchy children and internal children.
The hypotheses refer only to whole-pair uniformity and to the sizes of the
actual source/target subreservoirs. -/
theorem card_targetCoordinateRemoved_le
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (i : Fin s) (a : Fin (F.segments.size i))
    (hsourceSubset :
      ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootRaw interiorRaw i a ⊆
        ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole i a)
    (hsourceLarge :
      rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole i a) ≤
        #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootRaw interiorRaw i a))
    (hchildUniform : ∀ t ∈ childSegments F i a,
      G.IsUniform rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole i a)
        (rootWhole (rootGroup t)))
    (hchildSubset : ∀ t ∈ childSegments F i a,
      rootRaw (rootGroup t) ⊆ rootWhole (rootGroup t))
    (hchildLarge : ∀ t ∈ childSegments F i a,
      rho * #(rootWhole (rootGroup t)) ≤ #(rootRaw (rootGroup t)))
    (hinternalUniform : ∀ b ∈ internalTargets F i a,
      G.IsUniform rho
        (ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole i a)
        (interiorWhole i b))
    (hinternalSubset : ∀ b ∈ internalTargets F i a,
      interiorRaw i b ⊆ interiorWhole i b)
    (hinternalLarge : ∀ b ∈ internalTargets F i a,
      rho * #(interiorWhole i b) ≤ #(interiorRaw i b)) :
    (#(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw i a) : ℝ) ≤
      (∑ t ∈ childSegments F i a,
        rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole i a)) +
      ∑ b ∈ internalTargets F i a,
        rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole i a) := by
  classical
  let sourceWhole :=
    ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
      F rootGroup rootWhole interiorWhole i a
  let sourceRaw :=
    ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
      F rootGroup rootRaw interiorRaw i a
  let childRemoved := (childSegments F i a).biUnion fun t ↦
    targetLowDegreeVertices G rho sourceWhole (rootWhole (rootGroup t))
      sourceRaw (rootRaw (rootGroup t))
  let internalRemoved := (internalTargets F i a).biUnion fun b ↦
    targetLowDegreeVertices G rho sourceWhole (interiorWhole i b)
      sourceRaw (interiorRaw i b)
  have hchildCard : (#childRemoved : ℝ) ≤
      ∑ t ∈ childSegments F i a, rho * #sourceWhole := by
    have hunionNat : #childRemoved ≤
        ∑ t ∈ childSegments F i a,
          #(targetLowDegreeVertices G rho sourceWhole
            (rootWhole (rootGroup t)) sourceRaw (rootRaw (rootGroup t))) := by
      exact Finset.card_biUnion_le
    have hunion : (#childRemoved : ℝ) ≤
        ∑ t ∈ childSegments F i a,
          (#(targetLowDegreeVertices G rho sourceWhole
            (rootWhole (rootGroup t)) sourceRaw
              (rootRaw (rootGroup t))) : ℝ) := by
      exact_mod_cast hunionNat
    refine hunion.trans ?_
    apply Finset.sum_le_sum
    intro t ht
    exact card_targetLowDegreeVertices_le G (hchildUniform t ht)
      (by simpa only [sourceRaw, sourceWhole] using hsourceSubset)
      (hchildSubset t ht)
      (by simpa only [sourceRaw, sourceWhole] using hsourceLarge)
      (hchildLarge t ht)
  have hinternalCard : (#internalRemoved : ℝ) ≤
      ∑ b ∈ internalTargets F i a, rho * #sourceWhole := by
    have hunionNat : #internalRemoved ≤
        ∑ b ∈ internalTargets F i a,
          #(targetLowDegreeVertices G rho sourceWhole (interiorWhole i b)
            sourceRaw (interiorRaw i b)) := by
      exact Finset.card_biUnion_le
    have hunion : (#internalRemoved : ℝ) ≤
        ∑ b ∈ internalTargets F i a,
          (#(targetLowDegreeVertices G rho sourceWhole (interiorWhole i b)
            sourceRaw (interiorRaw i b)) : ℝ) := by
      exact_mod_cast hunionNat
    refine hunion.trans ?_
    apply Finset.sum_le_sum
    intro b hb
    exact card_targetLowDegreeVertices_le G (hinternalUniform b hb)
      (by simpa only [sourceRaw, sourceWhole] using hsourceSubset)
      (hinternalSubset b hb)
      (by simpa only [sourceRaw, sourceWhole] using hsourceLarge)
      (hinternalLarge b hb)
  have hunionNat : #(childRemoved ∪ internalRemoved) ≤
      #childRemoved + #internalRemoved := Finset.card_union_le _ _
  have hunion : (#(childRemoved ∪ internalRemoved) : ℝ) ≤
      (#childRemoved : ℝ) + (#internalRemoved : ℝ) := by
    exact_mod_cast hunionNat
  change (#(childRemoved ∪ internalRemoved) : ℝ) ≤ _
  exact hunion.trans (add_le_add hchildCard hinternalCard)

/-- Adding the fixed original-image reservation costs at most its literal
cardinality on top of the target-relative cleaning budget. -/
theorem card_targetCoordinateRemoved_union_le
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) (a : Fin (F.segments.size i))
    (hremoved :
      (#(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
        interiorWhole interiorRaw i a) : ℝ) ≤
        (∑ t ∈ childSegments F i a,
          rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootWhole interiorWhole i a)) +
        ∑ b ∈ internalTargets F i a,
          rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootWhole interiorWhole i a)) :
    (#(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
        interiorWhole interiorRaw i a ∪ reserved) : ℝ) ≤
      (∑ t ∈ childSegments F i a,
        rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole i a)) +
      (∑ b ∈ internalTargets F i a,
        rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole i a)) + #reserved := by
  have hcardNat := Finset.card_union_le
    (targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
      interiorWhole interiorRaw i a) reserved
  have hcard :
      (#(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
        interiorWhole interiorRaw i a ∪ reserved) : ℝ) ≤
        (#(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
          interiorWhole interiorRaw i a) : ℝ) + #reserved := by
    exact_mod_cast hcardNat
  linarith

/-- For a genuine non-root target, `targetInteriorRemoved` is exactly the
target-relative union plus the fixed reservation. -/
theorem card_targetInteriorRemoved_le
    [Fintype B] [DecidableEq B]
    (F : HierarchicalSegmentForest r s)
    (G : SimpleGraph B) [DecidableRel G.Adj] (rho : ℝ)
    (rootGroup : Fin s → RootGroup)
    (rootWhole rootRaw : RootGroup → Finset B)
    (interiorWhole interiorRaw :
      (i : Fin s) → Fin (F.segments.size i) → Finset B)
    (reserved : Finset B)
    (i : Fin s) (a : Fin (F.segments.size i))
    (ha : a ≠ F.segments.root i)
    (hremoved :
      (#(targetCoordinateRemoved F G rho rootGroup rootWhole rootRaw
        interiorWhole interiorRaw i a) : ℝ) ≤
        (∑ t ∈ childSegments F i a,
          rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootWhole interiorWhole i a)) +
        ∑ b ∈ internalTargets F i a,
          rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
            F rootGroup rootWhole interiorWhole i a)) :
    (#(targetInteriorRemoved F G rho rootGroup rootWhole rootRaw
        interiorWhole interiorRaw reserved i a) : ℝ) ≤
      (∑ t ∈ childSegments F i a,
        rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole i a)) +
      (∑ b ∈ internalTargets F i a,
        rho * #(ZhaoLemma59HierarchicalRegular.HierarchicalSegmentForest.rawCandidate
          F rootGroup rootWhole interiorWhole i a)) + #reserved := by
  rw [targetInteriorRemoved, if_neg ha]
  exact card_targetCoordinateRemoved_union_le F G rho rootGroup rootWhole
    rootRaw interiorWhole interiorRaw reserved i a hremoved

end HierarchicalSegmentForest

end Erdos547b.ZhaoLemma59HierarchicalTargetRemovalBounds

#print axioms Erdos547b.ZhaoLemma59HierarchicalTargetRemovalBounds.HierarchicalSegmentForest.card_targetCoordinateRemoved_le
