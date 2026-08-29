/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedRootAnchorOutcome

/-!
# Deleted-head classification of an unrooted active trace initial

The selected trace of a reserved active request starts on a grounded
limiting-ladder parent.  Its canonical prefix starts at a genuine original
source different from the reserved source.  Therefore an unrooted trace
initial has a last deleted head on that prefix.  In the pre-stopped relation
the deleted incoming edge is exactly a cut edge, a selected backward edge,
or a forward-conflict edge.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open GroundingErasedDecode GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- Positive finite data behind the `initial` constructor of an active
anchor failure. -/
structure ReservedActiveInitialLastDeletedHeadData
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V)) where
  parent : Gamma.DPath
  rootPath : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph
  parent_inessential : parent ∈ Gamma.inessentialPaths L.limitWarp
  rootPath_start : rootPath.start ∈ Gamma.source \ {R.record.initial}
  rootPath_finish : rootPath.finish =
    (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest d.1)).initial
  rootPath_support : rootPath.support ⊆ parent.support
  rootPath_edges : rootPath.edgeSet ⊆ parent.edgeSet
  deleted : LastDeletedHead rootPath
    (L.assertion822ReservedPreStoppedEdges hL S R)
  deleted_head_not_rooted : ¬ ∃ a ∈
    Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R)
        a deleted.head
  deleted_class :
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ GroundingCut.CE
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ erasedSelectedDirectionEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅ .backward) ∨
    (∃ u, (u, deleted.head) ∈ rootPath.edgeSet ∧
      (u, deleted.head) ∈ forwardConflictCutEdgesAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅)

/-- An unrooted selected trace initial gives the exact finite deleted-head
certificate above. -/
theorem exists_reservedActiveInitialLastDeletedHeadData
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (d : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    (hnot : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R)
        a (selectedRequestTrace (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (chosenRequest d.1)).initial) :
    Nonempty (ReservedActiveInitialLastDeletedHeadData d) := by
  obtain ⟨parent, q, hparent, hqStart, hqFinish, hqSupport, hqEdges⟩ :=
    R.exists_reservedSelectedRequest_rootPrefix (chosenRequest d.1)
  have hstart : ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R) a q.start :=
    ⟨q.start, hqStart, .refl⟩
  have hfinish : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          L.assertion822ReservedPreStoppedEdges hL S R) a q.finish := by
    intro hroot
    apply hnot
    simpa only [hqFinish] using hroot
  obtain ⟨D, hDnot⟩ :=
    exists_unrootedLastDeletedHead q hstart hfinish
  have hqFamily : q.edgeSet ⊆
      (L.popularAuxiliaryInput hL.legal).familyEdges := by
    intro e he
    refine ⟨parent, ?_, hqEdges he⟩
    simpa only [KappaLadder.popularAuxiliaryInput] using hparent.1
  have hclass := D.exists_classified_deletedIncomingPreStopped
    (L.reservedGroundedControls hL S R) hqFamily
  exact ⟨{
    parent := parent
    rootPath := q
    parent_inessential := hparent
    rootPath_start := hqStart
    rootPath_finish := hqFinish
    rootPath_support := hqSupport
    rootPath_edges := hqEdges
    deleted := D
    deleted_head_not_rooted := hDnot
    deleted_class := hclass }⟩

end Assertion822PreStoppedRootObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.exists_reservedActiveInitialLastDeletedHeadData
