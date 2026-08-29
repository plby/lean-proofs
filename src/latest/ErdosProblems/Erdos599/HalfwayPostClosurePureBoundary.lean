/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureFracturedAssignment

/-!+# Actual post-closure boundary alignment from interval purity

The canonical reference intervals need not be members of the later row.
Both families have the same two frontier boundaries, and each reference
interval meets these boundaries only at its endpoints.  That is enough:
outside the cutting set, a cut initial or terminal is an initial or terminal
of the original row.  No exceptional-component containment in the earlier
closing set is assumed.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open _root_.Erdos599.DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {Y W : Set Gamma.DPath} {X A B : Set V}

/-- Away from the cutting set a cut terminal was already a terminal of
the original row. -/
theorem cutTerminal_sdiff_subset_terminalFrontier
    (hW : Gamma.IsWarp W) :
    CutSplit.terminalVertices (outsideCarrier W X)
          (outsideFamilyEdges W X) X \ X ⊆
      Gamma.terminalFrontier W := by
  rintro x ⟨hxCut, hxNotX⟩
  rcases hxCut with hxEntry | hxOutside
  · exact False.elim (hxNotX hxEntry.1)
  · rw [isWarp_terminalFrontier_eq_noOutgoing hW]
    refine ⟨FocusedInsideCut.outsideCarrier_subset_vertexSet W X
      hxOutside.1, ?_⟩
    rintro ⟨y, hxy⟩
    apply hxOutside.2.2
    exact ⟨y, hxy, fun hboth => hxNotX hboth.1⟩

/-- Endpoint purity, rather than literal retention of reference members,
provides the boundary data for the actual holes. -/
theorem OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.boundaryData_of_pure_boundaries
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) W X)
    (hW : Gamma.IsWarp W)
    (hWinitial : Gamma.initialSet W = A)
    (hWterminal : Gamma.terminalFrontier W ⊆ B)
    (hYinitial : Gamma.initialSet Y ⊆ A)
    (hYsourcePure : ∀ p ∈ Y, ∀ x ∈ p.support, x ∈ A → x = p.initial)
    (hYtargetPure : ∀ p ∈ Y, ∀ x ∈ p.support, x ∈ B →
      Gamma.terminal? p = some x) :
    BoundaryAligned F.outside.holes.paths (outsideReference Y X) ∧
      Gamma.initialSet (outsideReference Y X) ⊆
        Gamma.initialSet F.outside.holes.paths := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [F.outside.initialSet_eq]
    rintro x ⟨hxCut, p, hp, hxp⟩
    have hxNotX : x ∉ X := Set.disjoint_left.1 hp.2 hxp
    have hxA : x ∈ A := by
      rw [← hWinitial]
      exact cutInitial_sdiff_subset_initialSet hW ⟨hxCut, hxNotX⟩
    exact ⟨p, hp, (hYsourcePure p hp.1 x hxp hxA).symm⟩
  · rw [F.outside.terminalFrontier_eq]
    rintro x ⟨hxCut, p, hp, hxp⟩
    have hxNotX : x ∉ X := Set.disjoint_left.1 hp.2 hxp
    have hxB : x ∈ B := hWterminal
      (cutTerminal_sdiff_subset_terminalFrontier hW ⟨hxCut, hxNotX⟩)
    exact ⟨p, hp, hYtargetPure p hp.1 x hxp hxB⟩
  · rw [F.outside.initialSet_eq]
    rintro x ⟨p, hp, rfl⟩
    have hxNotX : p.initial ∉ X :=
      Set.disjoint_left.1 hp.2 p.initial_mem_support
    have hxW : p.initial ∈ Gamma.initialSet W := by
      rw [hWinitial]
      exact hYinitial ⟨p, hp.1, rfl⟩
    have hxCarrier : p.initial ∈ Gamma.vertexSet W := by
      obtain ⟨q, hqW, hqx⟩ := hxW
      exact ⟨q, hqW, hqx ▸ q.initial_mem_support⟩
    apply Or.inr
    refine ⟨Or.inl ⟨hxCarrier, hxNotX⟩, hxNotX, ?_⟩
    rintro ⟨y, hyx⟩
    exact isWarp_noIncoming_familyEdges_of_mem_initialSet hW hxW
      ⟨y, outsideFamilyEdges_subset W X hyx⟩

namespace PostClosureIntervalTransaction

variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ X0 : Set V} {z : V}
variable {R : DynamicMoving931GlobalClosure C globalZ X0}

/-- Literal canonical survivor intervals meet the current frontier only
at their own initial vertex. -/
theorem intervalReference_source_pure
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    {p : Gamma.DPath} (hp : p ∈ T.intervalReference)
    {x : V} (hxp : x ∈ p.support)
    (hx : x ∈ R.capturedGeometry.oldSlice) : x = p.initial := by
  change p ∈ _root_.Erdos599.CardinalInduction.SliceSegmentCore.liftStageFamily
    R.capturedGeometry.ladder R.capturedGeometry.oldStage
      R.capturedGeometry.deferredOldStageOrdinaryFamily at hp
  rw [R.capturedGeometry.liftStageFamily_deferredOldStageOrdinaryFamily] at hp
  obtain ⟨a, rfl⟩ := hp
  exact Set.mem_singleton_iff.mp
    ((R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.segment_source a) ▸
      (show x ∈
        (R.capturedGeometry.deferredOldStageRealization.toSegmentRealization.segment a).support ∩
          R.capturedGeometry.oldSlice from ⟨hxp, hx⟩))

/-- Literal canonical survivor intervals meet the captured later frontier
only at their finite terminal. -/
theorem intervalReference_target_pure
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    _root_.Erdos599.CardinalInduction.SliceSpliceSource.MeetsOnlyAtTerminal
      Gamma T.intervalReference R.capturedGeometry.newSlice := by
  exact _root_.Erdos599.CardinalInduction.SliceDeltaLift.meetsOnlyAtTerminal_liftStageFamily
    R.capturedGeometry.deferredOldStageOrdinaryFamily_meetsOnlyAtTerminal

/-- The actual post-closure row and canonical interval reference satisfy
the fractured theorem's boundary hypotheses with no retention premise. -/
theorem boundaryData_of_interval_purity
    (T : PostClosureIntervalTransaction C globalZ X0 z R)
    (F : OutsideSplitWarp.SplitProjectedOutsideFracturedWarp
      (Gamma := Gamma) T.interval.ambientInterval R.closedSet) :
    BoundaryAligned F.outside.holes.paths
        (outsideReference T.intervalReference R.closedSet) ∧
      Gamma.initialSet (outsideReference T.intervalReference R.closedSet) ⊆
        Gamma.initialSet F.outside.holes.paths := by
  apply F.boundaryData_of_pure_boundaries
    T.interval.ambientInterval_linkage.isWarp
    T.interval.ambientInterval_linkage.initialSet_eq
    T.interval.ambientInterval_linkage.terminalFrontier_subset
  · rw [T.intervalReference_isLinkageBetween.initialSet_eq]
    exact Set.sdiff_subset
  · intro p hp x hxp hx
    exact T.intervalReference_source_pure hp hxp hx
  · exact T.intervalReference_target_pure

/-- Construct the actual bracket-preserving fractured assignment for the
post-closure interval, without assuming the newly selected exceptional
components are contained in the earlier closed set. -/
theorem exists_bracketFracturedAssignment_of_interval_purity
    (T : PostClosureIntervalTransaction C globalZ X0 z R) :
    Nonempty (PostClosureBracketFracturedAssignment T) := by
  obtain ⟨F⟩ := exists_splitProjectedOutsideFracturedWarp
    T.interval.ambientInterval R.closedSet
    T.interval.ambientInterval_linkage.isWarp
    T.interval.ambientInterval_linkage.finiteCharacter
  obtain ⟨hboundary, hinitial⟩ := T.boundaryData_of_interval_purity F
  have hOutsideWarp : Gamma.IsWarp
      (outsideReference T.intervalReference R.closedSet) :=
    T.intervalReference_isLinkageBetween.isWarp.subset
      (outsideReference_subset (Y := T.intervalReference) (X := R.closedSet))
  obtain ⟨A⟩ := F.outside.exists_bracketFracturedAssignment_anyReference
    hboundary hOutsideWarp hinitial
  exact ⟨{ fractured := F, assignment := A }⟩

end PostClosureIntervalTransaction

#print axioms OutsideSplitWarp.SplitProjectedOutsideFracturedWarp.boundaryData_of_pure_boundaries
#print axioms PostClosureIntervalTransaction.boundaryData_of_interval_purity
#print axioms PostClosureIntervalTransaction.exists_bracketFracturedAssignment_of_interval_purity

end Erdos599.Blueprint.LinkageBlueprint
