/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafePostClosureEndpointExposure
import ErdosProblems.Erdos599.HalfwayPostClosureWholeOwnerInterval
import ErdosProblems.Erdos599.HalfwayPostClosureSegmentedRoof

/-!
# Whole-owner interval normalization for the native moving closure

The completed current-to-later row is mixed componentwise with the full
canonical finite interval reference.  Outside one `kappa`-small alternating
component, the normalized row is literally the canonical reference row.
This is the honest component exchange needed before selecting continuations:
it prevents independent, colliding suffix choices on the same reference
owner.  No finite-character assertion is made about the limiting warp.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath
open _root_.Erdos599.Alternating
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.SliceCandidate
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

/-- Roots at which the completed interval row may differ from the canonical
ordinary interval row. -/
def nativeWholeOwnerSeed
    (T : NativePostClosureIntervalTransaction C seed z R) : Set V :=
  ((nativeCapturedGeometry R).deferredOldStageExceptional ∪ {z}) ∪
    oldStageContactInitials (nativeCapturedGeometry R) T.interval.safe

/-- The alternating owner component changed by native normalization. -/
def nativeWholeOwnerComponent
    (T : NativePostClosureIntervalTransaction C seed z R) : Set V :=
  exceptionalComponentVertices Gamma T.interval.ambientInterval
    T.intervalReference T.nativeWholeOwnerSeed

/-- The native whole-owner normalized current-to-later row. -/
def nativeWholeOwnerInterval
    (T : NativePostClosureIntervalTransaction C seed z R) :
    Set Gamma.DPath :=
  componentMixedFamily Gamma T.interval.ambientInterval
    T.intervalReference T.nativeWholeOwnerSeed

theorem nativeWholeOwnerSeed_subset_exceptionalComponents
    (T : NativePostClosureIntervalTransaction C seed z R) :
    T.nativeWholeOwnerSeed ⊆ T.interval.exceptionalComponents := by
  simpa only [nativeWholeOwnerSeed] using
    T.interval.excludedInitials_subset_exceptional

theorem nativeWholeOwnerSeed_card_le
    (T : NativePostClosureIntervalTransaction C seed z R) :
    #T.nativeWholeOwnerSeed ≤ kappa := by
  exact (Cardinal.mk_subtype_mono
    T.nativeWholeOwnerSeed_subset_exceptionalComponents).trans
      T.interval.exceptionalComponents_card

theorem nativeWholeOwnerSeed_subset_oldSlice
    (T : NativePostClosureIntervalTransaction C seed z R) :
    T.nativeWholeOwnerSeed ⊆ (nativeCapturedGeometry R).oldSlice := by
  rintro x ((hxExceptional | hxz) | hxContact)
  · exact hxExceptional.1
  · exact Set.mem_singleton_iff.1 hxz ▸ T.interval.source_mem
  · simp only [oldStageContactInitials] at hxContact
    obtain ⟨p, hpMeeting, rfl⟩ := hxContact
    have hpInitial : p.initial ∈
        ((nativeCapturedGeometry R).ladder.stageWeb
          (nativeCapturedGeometry R).oldStage).initialSet
          (nativeCapturedGeometry R).deferredOldStageOrdinaryFamily :=
      ⟨p, hpMeeting.1, rfl⟩
    rw [(nativeCapturedGeometry R).deferredOldStageOrdinaryFamily_isLinkageBetween.initialSet_eq]
      at hpInitial
    exact hpInitial.1

/-- The normalized native row retains the exact current/later boundary. -/
theorem nativeWholeOwnerInterval_isLinkageBetween
    (T : NativePostClosureIntervalTransaction C seed z R) :
    IsLinkageBetween Gamma (nativeCapturedGeometry R).oldSlice
      (nativeCapturedGeometry R).newSlice
      T.nativeWholeOwnerInterval := by
  apply componentMixedFamily_isLinkageBetween_of_partial_complement Gamma
    T.interval.ambientInterval_linkage
    T.intervalReference_isLinkageBetween
  · intro x hx
    exact Or.inl (Or.inl hx)
  · exact T.nativeWholeOwnerSeed_subset_oldSlice

/-- The entire changed owner component is `kappa`-small. -/
theorem nativeWholeOwnerComponent_card_le
    (T : NativePostClosureIntervalTransaction C seed z R) :
    #T.nativeWholeOwnerComponent ≤ kappa := by
  apply lt_succ_iff.mp
  apply mk_exceptionalComponentVertices_lt
    (Cardinal.isRegular_succ C.capacity_infinite)
    (C.capacity_infinite.trans_lt (lt_succ kappa))
    T.interval.ambientInterval_linkage.isWarp
    T.intervalReference_isLinkageBetween.isWarp
    T.interval.ambientInterval_linkage.finiteCharacter
    T.intervalReference_isLinkageBetween.finiteCharacter
  exact lt_succ_iff.mpr T.nativeWholeOwnerSeed_card_le

theorem nativeWholeOwnerInterval_subset_union
    (T : NativePostClosureIntervalTransaction C seed z R) :
    T.nativeWholeOwnerInterval ⊆
      T.interval.ambientInterval ∪ T.intervalReference := by
  rintro p (hp | hp)
  · exact Or.inl hp.1
  · exact Or.inr hp.1

/-- The canonical native interval reference lies under its later frontier. -/
theorem nativeIntervalReference_vertices_subset_capturedRoof
    (T : NativePostClosureIntervalTransaction C seed z R) :
    Gamma.vertexSet T.intervalReference ⊆
      (nativeCapturedGeometry R).outerRoof := by
  apply CardinalInduction.SliceRestrictedDelta.linkage_vertexSet_subset_roof_of_initial
    Gamma T.intervalReference_isLinkageBetween
  · intro x hx
    exact C.legal.frontierChronology R.later.current_lt hx.1
  · exact T.intervalReference_target_pure

/-- No vertex is introduced above the captured later roof. -/
theorem nativeWholeOwnerInterval_vertices_subset_capturedRoof
    (T : NativePostClosureIntervalTransaction C seed z R) :
    Gamma.vertexSet T.nativeWholeOwnerInterval ⊆
      (nativeCapturedGeometry R).outerRoof := by
  rintro x ⟨p, hp, hxp⟩
  rcases T.nativeWholeOwnerInterval_subset_union hp with hpW | hpY
  · exact T.interval.ambientInterval_in_outerRoof p hpW hxp
  · exact T.nativeIntervalReference_vertices_subset_capturedRoof ⟨p, hpY, hxp⟩

/-- Both sides of the component exchange remain tight at the later
frontier. -/
theorem nativeWholeOwnerInterval_meetsOnlyAtTerminal
    (T : NativePostClosureIntervalTransaction C seed z R) :
    SliceSpliceSource.MeetsOnlyAtTerminal Gamma
      T.nativeWholeOwnerInterval (nativeCapturedGeometry R).newSlice := by
  intro p hp x hxp hxSlice
  rcases hp with hpW | hpY
  · exact T.interval.ambientInterval_meetsOnlyAtTerminal p hpW.1 x hxp hxSlice
  · exact T.intervalReference_target_pure p hpY.1 x hxp hxSlice

/-- Every canonical owner outside the changed component is retained
literally in the normalized row. -/
theorem intervalReference_mem_nativeWholeOwnerInterval_of_initial_not_component
    (T : NativePostClosureIntervalTransaction C seed z R)
    {p : Gamma.DPath} (hp : p ∈ T.intervalReference)
    (hinitial : p.initial ∉ T.nativeWholeOwnerComponent) :
    p ∈ T.nativeWholeOwnerInterval :=
  Or.inr ⟨hp, hinitial⟩

/-- Conversely, a canonical interval omitted by the normalized row has its
initial in the explicit changed component. -/
theorem intervalReference_initial_mem_component_of_not_mem_nativeWholeOwner
    (T : NativePostClosureIntervalTransaction C seed z R)
    {p : Gamma.DPath} (hp : p ∈ T.intervalReference)
    (hnot : p ∉ T.nativeWholeOwnerInterval) :
    p.initial ∈ T.nativeWholeOwnerComponent := by
  by_contra hinitial
  exact hnot
    (T.intervalReference_mem_nativeWholeOwnerInterval_of_initial_not_component
      hp hinitial)

/-- A member of a warp which is wholly contained in the cut has no retained
outside edge leaving any of its vertices.  Warp disjointness is essential:
it identifies the owner of a putative outside edge with the contained
member. -/
theorem no_outsideOutgoing_of_member_support_subset
    {W : Set Gamma.DPath} {X : Set V} (hW : Gamma.IsWarp W)
    {p : Gamma.DPath} (hp : p ∈ W) (hpX : p.support ⊆ X)
    {x : V} (hxp : x ∈ p.support) :
    ¬ ∃ y, (x, y) ∈ outsideFamilyEdges W X := by
  rintro ⟨y, hxy⟩
  have hxyFamily := hxy.1
  simp only [_root_.Erdos599.Alternating.familyEdges, Set.mem_iUnion]
    at hxyFamily
  obtain ⟨q, hq, hxyq⟩ := hxyFamily
  have hxq : x ∈ q.support := q.edgeSet_subset_support_prod hxyq |>.1
  have hqp : q = p :=
    DWeb.IsWarp.eq_of_mem_support hW hq hp hxq hxp
  subst q
  exact hxy.2 ⟨hpX (p.edgeSet_subset_support_prod hxyq).1,
    hpX (p.edgeSet_subset_support_prod hxyq).2⟩

/-- A cut initial lying in the closed set and on a canonical interval must
belong to an interval whose initial lies in the changed owner component.
Outside that component the interval is retained literally, whole-reference
closure puts it entirely in the cut, and hence it cannot emit an outside
edge.  This is the concrete component-exchange reduction of the covered
source problem. -/
theorem intervalReference_owner_initial_mem_component_of_cutInitial
    (T : NativePostClosureIntervalTransaction C seed z R)
    {x : V}
    (hxCut : x ∈ CutSplit.initialVertices
      (outsideCarrier T.nativeWholeOwnerInterval R.closedSet)
      (outsideFamilyEdges T.nativeWholeOwnerInterval R.closedSet)
      R.closedSet)
    (hxClosed : x ∈ R.closedSet)
    (hxReference : x ∈ Gamma.vertexSet T.intervalReference) :
    ∃ p ∈ T.intervalReference,
      x ∈ p.support ∧ p.initial ∈ T.nativeWholeOwnerComponent := by
  obtain ⟨p, hp, hxp⟩ := hxReference
  refine ⟨p, hp, hxp, ?_⟩
  by_contra hpInitial
  have hpRow : p ∈ T.nativeWholeOwnerInterval :=
    T.intervalReference_mem_nativeWholeOwnerInterval_of_initial_not_component
      hp hpInitial
  have hpClosed : p.support ⊆ R.closedSet :=
    T.intervalReference_closedUnderPaths p hp ⟨x, hxp, hxClosed⟩
  have hno := no_outsideOutgoing_of_member_support_subset
    T.nativeWholeOwnerInterval_isLinkageBetween.isWarp hpRow hpClosed hxp
  rcases hxCut with hxExit | hxOutside
  · exact hno hxExit.2
  · exact hxOutside.2.1 hxClosed

#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerInterval_isLinkageBetween
#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerComponent_card_le
#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerInterval_vertices_subset_capturedRoof
#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerInterval_meetsOnlyAtTerminal
#print axioms NativePostClosureIntervalTransaction.intervalReference_initial_mem_component_of_not_mem_nativeWholeOwner
#print axioms NativePostClosureIntervalTransaction.intervalReference_owner_initial_mem_component_of_cutInitial

end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
