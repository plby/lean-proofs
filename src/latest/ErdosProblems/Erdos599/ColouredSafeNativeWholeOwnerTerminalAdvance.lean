/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeWholeOwnerReclosure
import ErdosProblems.Erdos599.ColouredSafeClosedOwnerContinuation
import ErdosProblems.Erdos599.RegularSliceSurvivors
import ErdosProblems.Erdos599.HalfwayDeferredStageIntervalBridge

/-!
# Terminal advance after native whole-owner reclosure

After reclosing strictly above the old captured stage, terminals of the old
normalized row split honestly into two classes.

* A terminal in the new closed set has a whole closed limiting owner, hence
  the finite-persistent/inessential dichotomy.
* A terminal outside the new closed set must survive to the new frontier.
  Otherwise its limiting owner is a roofed miss, hence belongs to the
  inessential carrier which the new closure has absorbed.

All outside terminals are advanced simultaneously by the canonical stage
interval realization.  Its carrier is disjoint from the new closed set, so
these continuations cannot collide with the changed owner component.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.SliceCandidate
open _root_.Erdos599.CardinalInduction.RegularSliceSurvivors
open _root_.Erdos599.CardinalInduction.DeferredStageInterval
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

/-- Old normalized-row terminals not absorbed by the new closure. -/
def nativeWholeOwnerOutsideTerminals
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed') : Set V :=
  Gamma.terminalFrontier T.nativeWholeOwnerInterval \ R'.closedSet

/-- A closed old terminal has one whole closed limiting owner and therefore
the exact finite-persistent/inessential classification at the new stage. -/
theorem closedTerminal_owner_classification
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    {t : V} (ht : t ∈ Gamma.terminalFrontier T.nativeWholeOwnerInterval)
    (htClosed : t ∈ R'.closedSet) :
    ∃ p ∈ C.ladder.limitWarp, t ∈ p.support ∧
      p.support ⊆ R'.closedSet ∧
      ((∃ f : FinitePath Gamma.graph,
          p = .inl f ∧ f.finish ∈ C.persistent ∧
            f.support ⊆ R'.closedSet) ∨
        p ∈ Gamma.inessentialPaths
          (C.ladder.warpAt R'.later.stage)) := by
  have htOld : t ∈ C.ladder.frontier R.later.stage := by
    exact T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset ht
  obtain ⟨p, hp, htp⟩ := C.exists_limitWarp_owner_of_mem_frontier htOld
  have hpClosed : p.support ⊆ R'.closedSet :=
    R'.reference_closed p hp ⟨t, htp, htClosed⟩
  exact ⟨p, hp, htp, hpClosed,
    ClosedLimitOwner.finite_persistent_owner_or_inessential
      R' hp hpClosed⟩

/-- An outside old terminal's limiting owner really hits the strictly later
frontier.  A miss would be in the absorbed inessential carrier. -/
theorem outsideTerminal_exists_limitOwner_hitting_later
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {t : V} (ht : t ∈ T.nativeWholeOwnerOutsideTerminals R') :
    ∃ p ∈ C.ladder.limitWarp, t ∈ p.support ∧
      p ∈ C.limitReferenceAtFrontier R'.later.stage := by
  have htOld : t ∈ C.ladder.frontier R.later.stage :=
    T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset ht.1
  obtain ⟨p, hp, htp⟩ := C.exists_limitWarp_owner_of_mem_frontier htOld
  have hpOld : p ∈ C.limitReferenceAtFrontier R.later.stage :=
    ⟨hp, t, htp, htOld⟩
  have hpLater : p ∈ C.limitReferenceAtFrontier R'.later.stage := by
    by_contra hmiss
    have hroofed : p ∈ C.roofedLimitReferenceMiss R'.later.stage :=
      C.forwardDifference_subset_roofedMiss hlater.le ⟨hpOld, hmiss⟩
    have hinessential : p ∈
        Gamma.inessentialPaths (C.ladder.warpAt R'.later.stage) :=
      C.mem_inessentialPaths_of_roofedLimitReferenceMiss
        R'.later.stage hroofed
    exact ht.2 (R'.inessential_subset ⟨p, hinessential, htp⟩)
  exact ⟨p, hp, htp, hpLater⟩

/-- Every outside terminal is a genuine survivor source from the old
captured stage to the new one. -/
theorem nativeWholeOwnerOutsideTerminals_subset_survivorSources
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    T.nativeWholeOwnerOutsideTerminals R' ⊆
      survivorSources Gamma C.ladder R.later.stage R'.later.stage := by
  intro t ht
  have htOld : t ∈ C.ladder.frontier R.later.stage :=
    T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset ht.1
  obtain ⟨p, hp, htp, hpLater⟩ :=
    T.outsideTerminal_exists_limitOwner_hitting_later R' hlater ht
  obtain ⟨left, hleft, hleftTerminal, hleftExt⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit
      C.legal hp htOld htp
  obtain ⟨v, hvp, hvLater⟩ := hpLater.2
  obtain ⟨right, hright, hrightTerminal, hrightExt⟩ :=
    ladderReference.exists_prefix_of_limitWarp_frontier_hit
      C.legal hp hvLater hvp
  obtain ⟨f, rfl⟩ := ladderReference.finiteCharacter hleft
  obtain ⟨g, rfl⟩ := ladderReference.finiteCharacter hright
  have hfgrows := warpAt_grows_of_le C.legal hlater.le
  obtain ⟨q, hq, hfq⟩ := hfgrows (.inl f) hleft.1
  have hqg : q = (Sum.inl g : Gamma.DPath) := by
    apply DWeb.IsWarp.eq_of_initial_eq Gamma
      (C.legal.warpStages (Ladder.Stage.toExtended R'.later.stage))
      hq hright.1
    calc
      q.initial = f.start := (Gamma.extends_initial hfq).symm
      _ = p.initial := Gamma.extends_initial hleftExt
      _ = g.start := (Gamma.extends_initial hrightExt).symm
  subst q
  exact ⟨htOld, f, g, hleft, hright,
    Option.some.inj hleftTerminal, hfq⟩

/-- Canonical simultaneous later intervals for every unabsorbed terminal. -/
noncomputable def nativeWholeOwnerOutsideTerminalRealization
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    StageIntervalRealization C.ladder R.later.stage R'.later.stage
      (T.nativeWholeOwnerOutsideTerminals R') :=
  stageIntervalRealizationOfSubset_of_geometry
    (T.nativeWholeOwnerOutsideTerminals_subset_survivorSources R' hlater)
    C.legal.roofsSourceAtStages C.legal.warpStages
    (warpAt_grows_of_le C.legal hlater.le)

/-- The simultaneous outside-terminal continuation is an exact ambient
linkage to the new frontier. -/
theorem nativeWholeOwnerOutsideTerminalFamily_isLinkageBetween
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    IsLinkageBetween Gamma (T.nativeWholeOwnerOutsideTerminals R')
      (C.ladder.frontier R'.later.stage)
      (SliceSegmentCore.segmentFamily
        (T.nativeWholeOwnerOutsideTerminalRealization R' hlater).toSegmentRealization) := by
  exact SliceSegmentCore.segmentFamily_isLinkageBetween
    (C.legal.warpStages (Ladder.Stage.toExtended R'.later.stage))
    (T.nativeWholeOwnerOutsideTerminalRealization R' hlater).toSegmentRealization

/-- Every simultaneous outside-terminal continuation avoids the new closed
set.  This is the collision-prevention fact: a meeting limiting owner would
be wholly closed, contradicting its outside source. -/
theorem nativeWholeOwnerOutsideTerminalFamily_disjoint_closedSet
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    Disjoint
      (Gamma.vertexSet (SliceSegmentCore.segmentFamily
        (T.nativeWholeOwnerOutsideTerminalRealization R' hlater).toSegmentRealization))
      R'.closedSet := by
  apply Set.disjoint_left.2
  rintro x ⟨q, ⟨t, rfl⟩, hxq⟩ hxClosed
  let E := T.nativeWholeOwnerOutsideTerminalRealization R' hlater
  have htNotClosed : t.1 ∉ R'.closedSet := t.2.2
  obtain ⟨p, hp, htp, _hpLater⟩ :=
    T.outsideTerminal_exists_limitOwner_hitting_later R' hlater t.2
  have htSegment : t.1 ∈ (E.toSegmentRealization.segment t).support := by
    rw [← E.toSegmentRealization.segment_start t]
    exact (E.toSegmentRealization.segment t).start_mem_support
  have htRight : t.1 ∈ (E.rightPrefix t).support :=
    (E.segment_subpath t).1 htSegment
  have hrightExt : Gamma.Extends
      (Sum.inl (E.rightPrefix t) : Gamma.DPath) p := by
    apply C.legal.extends_limitWarp_of_stage_intersects
      (E.right_mem t).1 hp
    exact ⟨t.1, htRight, htp⟩
  have hxOwner : x ∈ p.support :=
    Gamma.support_mono_of_extends hrightExt
      ((E.segment_subpath t).1 hxq)
  have hpClosed : p.support ⊆ R'.closedSet :=
    R'.reference_closed p hp ⟨x, hxOwner, hxClosed⟩
  exact htNotClosed (hpClosed htp)

#print axioms NativePostClosureIntervalTransaction.closedTerminal_owner_classification
#print axioms NativePostClosureIntervalTransaction.outsideTerminal_exists_limitOwner_hitting_later
#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerOutsideTerminals_subset_survivorSources
#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerOutsideTerminalFamily_isLinkageBetween
#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerOutsideTerminalFamily_disjoint_closedSet

end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
