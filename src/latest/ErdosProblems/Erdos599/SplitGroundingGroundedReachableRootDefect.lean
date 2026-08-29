/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReachableReservedReduction
import ErdosProblems.Erdos599.GroundingFiniteSourceRootAt

/-!
# Ambient root defects for the source-reachable grounded split boundary

Membership in the source-reachable boundary retains an ambient finite path
from an original source.  If its endpoint is not rooted in the canonical
pre-stopped switched relation, that path has a last deleted head.  An ambient
edge need not belong to the limiting-ladder family, so the exact normal form
keeps that alternative together with the three genuine family-edge deletion
classes.

For an essential reserved-root obstruction, the ambient prefix either starts
at the deliberately reserved source or starts at an allowed source and has
the same last-deleted-head normal form.  No false family provenance is imposed
on either prefix.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

private abbrev RootDefectInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev RootDefectIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

private abbrev RootDefectControls :=
  L.splitGroundedCanonicalControls hL hground S

private abbrev RootDefectRecord :=
  L.splitGroundedCanonicalUnusedRecord hL hground S

private abbrev RootDefectEdges :=
  L.splitGroundedCanonicalSwitchedEdgesAt hL hground S ∅

/-- If a finite path starts at a rooted point but its finish is not rooted,
then it has a last deleted head which is itself not rooted.  This local
version avoids importing the obsolete ordinary-legality realization cone. -/
private theorem exists_unrootedLastDeletedHead_splitReachable
    {E : Set (V × V)} {A : Set V}
    (p : FinitePath Gamma.graph)
    (hstart : ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.start)
    (hfinish : ¬ ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a p.finish) :
    ∃ D : LastDeletedHead p E,
      ¬ ∃ a ∈ A,
        Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a D.head := by
  have hdeleted : ∃ e ∈ p.edgeSet, e ∉ E := by
    by_contra hnone
    apply hfinish
    obtain ⟨a, ha, hastart⟩ := hstart
    refine ⟨a, ha, hastart.trans ?_⟩
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ p.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      by_contra hxyE
      exact hnone ⟨(x, y), hxy, hxyE⟩
    · exact Alternating.Walk.reflTransGen_edgeSet p.walk
  let D := (exists_lastDeletedHead p hdeleted).some
  refine ⟨D, ?_⟩
  rintro ⟨a, ha, haD⟩
  apply hfinish
  refine ⟨a, ha, haD.trans ?_⟩
  have hsuffix : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ E) D.suffix.start D.suffix.finish := by
    apply Relation.ReflTransGen.mono
      (r := fun x y ↦ (x, y) ∈ D.suffix.edgeSet)
      (p := fun x y ↦ (x, y) ∈ E)
    · intro x y hxy
      exact D.suffix_edgeSet_subset hxy
    · exact Alternating.Walk.reflTransGen_edgeSet D.suffix.walk
  exact D.suffix_finish ▸ (D.suffix_start ▸ hsuffix)

/-- A concrete ambient source prefix and its first obstruction when a
source-reachable boundary point is not rooted even from the whole source. -/
structure SplitGroundedWholeSourceAmbientLastDeletedHeadData
    (O : L.SplitGroundedReachableWholeSourceRootObstruction
      (RootDefectRecord (L := L) (hL := hL)
        (hground := hground) (S := S))) where
  path : FinitePath Gamma.graph
  path_start_source : path.start ∈ Gamma.source
  path_finish_boundary : path.finish = O.boundary
  deleted : LastDeletedHead path
    (RootDefectEdges (L := L) (hL := hL)
      (hground := hground) (S := S))
  deleted_head_not_rooted : ¬ ∃ a ∈ Gamma.source,
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ RootDefectEdges
        (L := L) (hL := hL) (hground := hground) (S := S))
      a deleted.head
  tail : V
  incoming_mem : (tail, deleted.head) ∈ path.edgeSet
  incoming_not_relation : (tail, deleted.head) ∉
    RootDefectEdges (L := L) (hL := hL)
      (hground := hground) (S := S)
  incoming_class :
    (tail, deleted.head) ∉
        (RootDefectInput (L := L) (hL := hL)).familyEdges ∨
      (tail, deleted.head) ∈ GroundingCut.CE
        (RootDefectInput (L := L) (hL := hL)) S.cut ∨
      (tail, deleted.head) ∈ erasedSelectedDirectionEdgesAt
        (RootDefectIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (RootDefectControls (L := L) (hL := hL)
          (hground := hground) (S := S)) ∅ .backward ∨
      (tail, deleted.head) ∈ forwardConflictCutEdgesAt
        (RootDefectIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (RootDefectControls (L := L) (hL := hL)
          (hground := hground) (S := S)) ∅

/-- Extract the exact last missing switched edge of the ambient prefix
stored by a whole-source root obstruction. -/
theorem SplitGroundedReachableWholeSourceRootObstruction.exists_ambientLastDeletedHeadData
    (O : L.SplitGroundedReachableWholeSourceRootObstruction
      (RootDefectRecord (L := L) (hL := hL)
        (hground := hground) (S := S))) :
    Nonempty (L.SplitGroundedWholeSourceAmbientLastDeletedHeadData O) := by
  obtain ⟨p, hpStart, hpFinish⟩ := O.exists_ambientPath_to_boundary
  have hstart : ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RootDefectEdges
          (L := L) (hL := hL) (hground := hground) (S := S))
        a p.start :=
    ⟨p.start, hpStart, .refl⟩
  have hfinish : ¬ ∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ RootDefectEdges
          (L := L) (hL := hL) (hground := hground) (S := S))
        a p.finish := by
    simpa only [hpFinish] using O.not_rooted
  obtain ⟨D, hDnot⟩ :=
    exists_unrootedLastDeletedHead_splitReachable p hstart hfinish
  obtain ⟨u, huPath, huNot⟩ := D.deleted_incoming
  have hclass :
      (u, D.head) ∉
          (RootDefectInput (L := L) (hL := hL)).familyEdges ∨
        (u, D.head) ∈ GroundingCut.CE
          (RootDefectInput (L := L) (hL := hL)) S.cut ∨
        (u, D.head) ∈ erasedSelectedDirectionEdgesAt
          (RootDefectIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (RootDefectControls (L := L) (hL := hL)
            (hground := hground) (S := S)) ∅ .backward ∨
        (u, D.head) ∈ forwardConflictCutEdgesAt
          (RootDefectIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (RootDefectControls (L := L) (hL := hL)
            (hground := hground) (S := S)) ∅ := by
    by_cases huFamily : (u, D.head) ∈
        (RootDefectInput (L := L) (hL := hL)).familyEdges
    · rcases familyEdge_deleted_classificationAt
          (RootDefectControls (L := L) (hL := hL)
            (hground := hground) (S := S)) (∅ : Set V)
          huFamily huNot with hcut | hbackward | hconflict | hboundary
      · exact Or.inr (Or.inl hcut)
      · exact Or.inr (Or.inr (Or.inl hbackward))
      · exact Or.inr (Or.inr (Or.inr hconflict))
      · rw [boundaryOutgoingCutEdgesAt_empty] at hboundary
        exact False.elim hboundary
    · exact Or.inl huFamily
  exact ⟨{
    path := p
    path_start_source := hpStart
    path_finish_boundary := hpFinish
    deleted := D
    deleted_head_not_rooted := hDnot
    tail := u
    incoming_mem := huPath
    incoming_not_relation := huNot
    incoming_class := hclass }⟩

/-- The allowed-source alternative of the ambient prefix retained by an
essential reserved-root obstruction. -/
structure SplitGroundedEssentialAllowedAmbientLastDeletedHeadData
    (O : L.SplitGroundedReachableEssentialReservedRootObstruction
      (hL := hL) (hground := hground) (S := S)) where
  path : FinitePath Gamma.graph
  path_start_allowed : path.start ∈ Gamma.source \ {
    (RootDefectRecord (L := L) (hL := hL)
      (hground := hground) (S := S)).record.initial}
  path_finish_boundary : path.finish = O.obstruction.boundary
  deleted : LastDeletedHead path
    (RootDefectEdges (L := L) (hL := hL)
      (hground := hground) (S := S))
  deleted_head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {
      (RootDefectRecord (L := L) (hL := hL)
        (hground := hground) (S := S)).record.initial},
    Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ RootDefectEdges
        (L := L) (hL := hL) (hground := hground) (S := S))
      a deleted.head
  tail : V
  incoming_mem : (tail, deleted.head) ∈ path.edgeSet
  incoming_not_relation : (tail, deleted.head) ∉
    RootDefectEdges (L := L) (hL := hL)
      (hground := hground) (S := S)
  incoming_class :
    (tail, deleted.head) ∉
        (RootDefectInput (L := L) (hL := hL)).familyEdges ∨
      (tail, deleted.head) ∈ GroundingCut.CE
        (RootDefectInput (L := L) (hL := hL)) S.cut ∨
      (tail, deleted.head) ∈ erasedSelectedDirectionEdgesAt
        (RootDefectIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (RootDefectControls (L := L) (hL := hL)
          (hground := hground) (S := S)) ∅ .backward ∨
      (tail, deleted.head) ∈ forwardConflictCutEdgesAt
        (RootDefectIndexed (L := L) (hL := hL)
          (hground := hground)) S
        (RootDefectControls (L := L) (hL := hL)
          (hground := hground) (S := S)) ∅

/-- Complete ambient-prefix dichotomy for an essential reserved-root
obstruction.  Starting at the reserved source is kept as the genuine
exchange case; every other start is an allowed source and exposes an exact
last-deleted-head datum. -/
inductive SplitGroundedEssentialReservedAmbientDefectOutcome
    (O : L.SplitGroundedReachableEssentialReservedRootObstruction
      (hL := hL) (hground := hground) (S := S)) : Prop
  | reservedPath
      (path : FinitePath Gamma.graph)
      (path_start_reserved : path.start =
        (RootDefectRecord (L := L) (hL := hL)
          (hground := hground) (S := S)).record.initial)
      (path_finish_boundary : path.finish = O.obstruction.boundary)
  | allowedDeleted
      (data : L.SplitGroundedEssentialAllowedAmbientLastDeletedHeadData O)

/-- Extract the complete ambient defect of an essential reserved-root
obstruction. -/
theorem SplitGroundedReachableEssentialReservedRootObstruction.ambientDefectOutcome
    (O : L.SplitGroundedReachableEssentialReservedRootObstruction
      (hL := hL) (hground := hground) (S := S)) :
    L.SplitGroundedEssentialReservedAmbientDefectOutcome O := by
  obtain ⟨p, hpStart, hpFinish⟩ :=
    O.obstruction.exists_ambientPath_to_boundary
  let R := RootDefectRecord
    (L := L) (hL := hL) (hground := hground) (S := S)
  by_cases hpReserved : p.start = R.record.initial
  · exact .reservedPath p hpReserved hpFinish
  · have hpAllowed : p.start ∈ Gamma.source \ {R.record.initial} :=
      ⟨hpStart, by simpa only [Set.mem_singleton_iff] using hpReserved⟩
    have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RootDefectEdges
            (L := L) (hL := hL) (hground := hground) (S := S))
          a p.start :=
      ⟨p.start, hpAllowed, .refl⟩
    have hfinish : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ RootDefectEdges
            (L := L) (hL := hL) (hground := hground) (S := S))
          a p.finish := by
      simpa only [hpFinish] using O.obstruction.not_rooted_from_allowed
    obtain ⟨D, hDnot⟩ :=
      exists_unrootedLastDeletedHead_splitReachable p hstart hfinish
    obtain ⟨u, huPath, huNot⟩ := D.deleted_incoming
    have hclass :
        (u, D.head) ∉
            (RootDefectInput (L := L) (hL := hL)).familyEdges ∨
          (u, D.head) ∈ GroundingCut.CE
            (RootDefectInput (L := L) (hL := hL)) S.cut ∨
          (u, D.head) ∈ erasedSelectedDirectionEdgesAt
            (RootDefectIndexed (L := L) (hL := hL)
              (hground := hground)) S
            (RootDefectControls (L := L) (hL := hL)
              (hground := hground) (S := S)) ∅ .backward ∨
          (u, D.head) ∈ forwardConflictCutEdgesAt
            (RootDefectIndexed (L := L) (hL := hL)
              (hground := hground)) S
            (RootDefectControls (L := L) (hL := hL)
              (hground := hground) (S := S)) ∅ := by
      by_cases huFamily : (u, D.head) ∈
          (RootDefectInput (L := L) (hL := hL)).familyEdges
      · rcases familyEdge_deleted_classificationAt
            (RootDefectControls (L := L) (hL := hL)
              (hground := hground) (S := S)) (∅ : Set V)
            huFamily huNot with hcut | hbackward | hconflict | hboundary
        · exact Or.inr (Or.inl hcut)
        · exact Or.inr (Or.inr (Or.inl hbackward))
        · exact Or.inr (Or.inr (Or.inr hconflict))
        · rw [boundaryOutgoingCutEdgesAt_empty] at hboundary
          exact False.elim hboundary
      · exact Or.inl huFamily
    exact .allowedDeleted {
      path := p
      path_start_allowed := hpAllowed
      path_finish_boundary := hpFinish
      deleted := D
      deleted_head_not_rooted := hDnot
      tail := u
      incoming_mem := huPath
      incoming_not_relation := huNot
      incoming_class := hclass }

/-- Lossless constructor-level split of a whole-source ambient defect.  The
external branch is intentionally retained: its edge lies in the ambient
graph but outside the limiting-ladder family, so no selected-owner theorem
may be applied to it. -/
inductive SplitGroundedWholeSourceAmbientDeletedHeadOutcome
    (O : L.SplitGroundedReachableWholeSourceRootObstruction
      (RootDefectRecord (L := L) (hL := hL)
        (hground := hground) (S := S)))
    (data : L.SplitGroundedWholeSourceAmbientLastDeletedHeadData O) : Prop
  | external
      (edge_not_family : (data.tail, data.deleted.head) ∉
        (RootDefectInput (L := L) (hL := hL)).familyEdges)
  | representedCut
      (edge_mem : (data.tail, data.deleted.head) ∈ GroundingCut.CE
        (RootDefectInput (L := L) (hL := hL)) S.cut)
  | selectedBackward
      (edge_mem : (data.tail, data.deleted.head) ∈
        erasedSelectedDirectionEdgesAt
          (RootDefectIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (RootDefectControls (L := L) (hL := hL)
            (hground := hground) (S := S)) ∅ .backward)
  | forwardConflict
      (edge_mem : (data.tail, data.deleted.head) ∈
        forwardConflictCutEdgesAt
          (RootDefectIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (RootDefectControls (L := L) (hL := hL)
            (hground := hground) (S := S)) ∅)

/-- Expose exactly one of the four constructors already certified by the
whole-source last-deleted-head datum. -/
theorem SplitGroundedWholeSourceAmbientLastDeletedHeadData.outcome
    {O : L.SplitGroundedReachableWholeSourceRootObstruction
      (RootDefectRecord (L := L) (hL := hL)
        (hground := hground) (S := S))}
    (data : L.SplitGroundedWholeSourceAmbientLastDeletedHeadData O) :
    L.SplitGroundedWholeSourceAmbientDeletedHeadOutcome O data := by
  rcases data.incoming_class with
      hexternal | hcut | hbackward | hconflict
  · exact .external hexternal
  · exact .representedCut hcut
  · exact .selectedBackward hbackward
  · exact .forwardConflict hconflict

/-- Constructor-level split of the allowed-source essential defect. -/
inductive SplitGroundedEssentialAllowedAmbientDeletedHeadOutcome
    (O : L.SplitGroundedReachableEssentialReservedRootObstruction
      (hL := hL) (hground := hground) (S := S))
    (data : L.SplitGroundedEssentialAllowedAmbientLastDeletedHeadData O) : Prop
  | external
      (edge_not_family : (data.tail, data.deleted.head) ∉
        (RootDefectInput (L := L) (hL := hL)).familyEdges)
  | representedCut
      (edge_mem : (data.tail, data.deleted.head) ∈ GroundingCut.CE
        (RootDefectInput (L := L) (hL := hL)) S.cut)
  | selectedBackward
      (edge_mem : (data.tail, data.deleted.head) ∈
        erasedSelectedDirectionEdgesAt
          (RootDefectIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (RootDefectControls (L := L) (hL := hL)
            (hground := hground) (S := S)) ∅ .backward)
  | forwardConflict
      (edge_mem : (data.tail, data.deleted.head) ∈
        forwardConflictCutEdgesAt
          (RootDefectIndexed (L := L) (hL := hL)
            (hground := hground)) S
          (RootDefectControls (L := L) (hL := hL)
            (hground := hground) (S := S)) ∅)

/-- Expose exactly one of the four constructors certified by an
allowed-source essential last-deleted-head datum. -/
theorem SplitGroundedEssentialAllowedAmbientLastDeletedHeadData.outcome
    {O : L.SplitGroundedReachableEssentialReservedRootObstruction
      (hL := hL) (hground := hground) (S := S)}
    (data : L.SplitGroundedEssentialAllowedAmbientLastDeletedHeadData O) :
    L.SplitGroundedEssentialAllowedAmbientDeletedHeadOutcome O data := by
  rcases data.incoming_class with
      hexternal | hcut | hbackward | hconflict
  · exact .external hexternal
  · exact .representedCut hcut
  · exact .selectedBackward hbackward
  · exact .forwardConflict hconflict

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReachableWholeSourceRootObstruction.exists_ambientLastDeletedHeadData
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedReachableEssentialReservedRootObstruction.ambientDefectOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedWholeSourceAmbientLastDeletedHeadData.outcome
