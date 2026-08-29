/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedReachableWholeSourceDeletedHead

/-!
# Ambient defects of a reachable essential reserved-root obstruction

The reachable-boundary reduction retains a finite ambient prefix to the
displayed essential boundary point.  If this prefix starts at the deliberately
reserved source, that fact is the exact residual exchange case.  Otherwise its
initial vertex is an allowed source, so failure of repaired reachability has a
last deleted head.  The incoming edge of that head is classified without
pretending that an arbitrary ambient edge belongs to the ladder family.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822ReachableEssentialReservedRootObstruction

/-- The allowed-source alternative of the ambient-prefix defect. -/
structure AllowedAmbientLastDeletedHeadData
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableEssentialReservedRootObstruction hL S R) where
  path : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph
  path_start_allowed : path.start ∈ Gamma.source \ {R.record.initial}
  path_finish_boundary : path.finish = O.obstruction.boundary
  deleted : LastDeletedHead path
    (L.assertion822ReservedPreStoppedEdges hL S R)
  deleted_head_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
    Relation.ReflTransGen
      (fun x y ↦
        (x, y) ∈ L.assertion822ReservedPreStoppedEdges hL S R)
      a deleted.head
  tail : V
  incoming_mem : (tail, deleted.head) ∈ path.edgeSet
  incoming_not_relation : (tail, deleted.head) ∉
    L.assertion822ReservedPreStoppedEdges hL S R
  incoming_class :
    (tail, deleted.head) ∉
        (L.popularAuxiliaryInput hL.legal).familyEdges ∨
      (tail, deleted.head) ∈ GroundingCut.CE
        (L.popularAuxiliaryInput hL.legal) S.cut ∨
      (tail, deleted.head) ∈ erasedSelectedDirectionEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅ .backward ∨
      (tail, deleted.head) ∈ forwardConflictCutEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅

/-- Complete pathwise dichotomy for a source-reachable essential reserved
root failure. -/
inductive AmbientDefectOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableEssentialReservedRootObstruction hL S R) : Prop
  | reservedPath
      (path : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph)
      (path_start_reserved : path.start = R.record.initial)
      (path_finish_boundary : path.finish = O.obstruction.boundary)
  | allowedDeleted (data : O.AllowedAmbientLastDeletedHeadData)

/-- Extract either the reserved ambient prefix or the exact final missing
edge of an allowed-source ambient prefix. -/
theorem ambientDefectOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822ReachableEssentialReservedRootObstruction hL S R) :
    O.AmbientDefectOutcome := by
  rcases O.reservedPath_or_exists_unrootedLastDeletedHead with
    ⟨p, hpReserved, hpFinish⟩ | ⟨p, hpAllowed, hpFinish, D, hDnot⟩
  · exact .reservedPath p hpReserved hpFinish
  · obtain ⟨u, huPath, huNot⟩ := D.deleted_incoming
    have hclass :
        (u, D.head) ∉
            (L.popularAuxiliaryInput hL.legal).familyEdges ∨
          (u, D.head) ∈ GroundingCut.CE
            (L.popularAuxiliaryInput hL.legal) S.cut ∨
          (u, D.head) ∈ erasedSelectedDirectionEdgesAt
            (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) ∅ .backward ∨
          (u, D.head) ∈ forwardConflictCutEdgesAt
            (L.popularAuxiliaryIndexed hL) S
            (L.reservedGroundedControls hL S R) ∅ := by
      by_cases huFamily : (u, D.head) ∈
          (L.popularAuxiliaryInput hL.legal).familyEdges
      · have hdeleted := familyEdge_deleted_classificationAt
          (L.reservedGroundedControls hL S R) (∅ : Set V)
          huFamily huNot
        rcases hdeleted with hcut | hback | hconflict | hboundary
        · exact Or.inr (Or.inl hcut)
        · exact Or.inr (Or.inr (Or.inl hback))
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

end Assertion822ReachableEssentialReservedRootObstruction

/-- Public reachable-boundary compiler whose two root callbacks receive the
concrete ambient defect in addition to the well-founded construction-specific
normal form.  No pathwise provenance needs to be reconstructed downstream. -/
theorem assertion822Output_or_hindrance_of_preStoppedReachableDefectRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairEssential : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822ReachableEssentialReservedRootObstruction hL S R),
      O.AmbientDefectOutcome →
      O.obstruction.BackwardSelfNormalizedFirstFragmentRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairWholeSource : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822ReachableWholeSourceRootObstruction hL S R),
      O.AmbientLastDeletedHeadData →
      O.obstruction.BackwardSelfNormalizedFirstFragmentRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822ReachableBoundaryObstruction hL S R),
      O.obstruction.FiniteSinkReducedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedReachableRepairs hL S
  · intro R O outcome
    exact repairEssential R O O.ambientDefectOutcome outcome
  · intro R O outcome
    exact repairWholeSource R O O.exists_ambientLastDeletedHeadData.some outcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822ReachableEssentialReservedRootObstruction.ambientDefectOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedReachableDefectRepairs
