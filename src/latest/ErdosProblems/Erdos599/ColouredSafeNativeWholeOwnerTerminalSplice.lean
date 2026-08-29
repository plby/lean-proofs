/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeWholeOwnerTerminalAdvance

/-!
# Splicing the native whole-owner row to its surviving continuations

The simultaneous continuation of the terminals outside the new closed set
is star-compatible with the entire old normalized row.  On the changed
alternating component this follows from closed-set disjointness.  Off that
component the old row is literally a canonical interval.  A contact with a
later interval identifies their common limiting-warp owner; below the old
frontier the owner is contained in the old stage prefix, whose intersection
with the later segment is exactly their common endpoint.

No continuation is asserted for terminals already in the closed set.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.Alternating
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.SliceCandidate
open _root_.Erdos599.CardinalInduction.RegularSliceSurvivors
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

/-- The old whole-owner normalized row can be spliced with all canonical
continuations whose sources remain outside the new closed carrier. -/
theorem nativeWholeOwnerOutsideTerminalFamily_starCompatible
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hcomponent : T.nativeWholeOwnerComponent ⊆ R'.closedSet) :
    Gamma.StarCompatible T.nativeWholeOwnerInterval
      (SliceSegmentCore.segmentFamily
        (T.nativeWholeOwnerOutsideTerminalRealization R' hlater).toSegmentRealization) := by
  let E := T.nativeWholeOwnerOutsideTerminalRealization R' hlater
  intro p hp q hq x hxp hxq
  obtain ⟨t, rfl⟩ := hq
  rcases hp with hpLeft | hpRight
  · have hpClosed : p.support ⊆ R'.closedSet :=
      (T.nativeWholeOwner_left_support_subset_component hpLeft).trans
        hcomponent
    have hxClosed : x ∈ R'.closedSet := hpClosed hxp
    have hxFamily : x ∈ Gamma.vertexSet
        (SliceSegmentCore.segmentFamily E.toSegmentRealization) :=
      ⟨Sum.inl (E.toSegmentRealization.segment t), ⟨t, rfl⟩, hxq⟩
    exact False.elim <| Set.disjoint_left.1
      (T.nativeWholeOwnerOutsideTerminalFamily_disjoint_closedSet R' hlater)
      hxFamily hxClosed
  · let ps : T.intervalReference := ⟨p, hpRight.1⟩
    let ownerP := T.intervalReferenceOwner ps
    have hownerP : ownerP ∈ C.ladder.limitWarp :=
      T.intervalReferenceOwner_mem ps
    have hxpOwnerP : x ∈ ownerP.support :=
      (T.intervalReference_subpath_owner ps).1 hxp
    obtain ⟨ownerQ, hownerQ, htOwnerQ, _hownerQLater⟩ :=
      T.outsideTerminal_exists_limitOwner_hitting_later R' hlater t.2
    have htSegment : t.1 ∈ (E.toSegmentRealization.segment t).support := by
      rw [← E.toSegmentRealization.segment_start t]
      exact (E.toSegmentRealization.segment t).start_mem_support
    have htRight : t.1 ∈ (E.rightPrefix t).support :=
      (E.segment_subpath t).1 htSegment
    have hrightExt : Gamma.Extends
        (Sum.inl (E.rightPrefix t) : Gamma.DPath) ownerQ := by
      apply C.legal.extends_limitWarp_of_stage_intersects
        (E.right_mem t).1 hownerQ
      exact ⟨t.1, htRight, htOwnerQ⟩
    have hxOwnerQ : x ∈ ownerQ.support :=
      Gamma.support_mono_of_extends hrightExt
        ((E.segment_subpath t).1 hxq)
    have howners : ownerP = ownerQ := by
      apply DWeb.IsWarp.eq_of_mem_support
        (C.legal.warpStages (Ladder.finalStage (succ kappa)))
        hownerP hownerQ hxpOwnerP hxOwnerQ
    have htLeft : t.1 ∈ (E.leftPrefix t).support := by
      rw [← E.left_finish t]
      exact (E.leftPrefix t).finish_mem_support
    have hleftExt : Gamma.Extends
        (Sum.inl (E.leftPrefix t) : Gamma.DPath) ownerQ := by
      apply C.legal.extends_limitWarp_of_stage_intersects
        (E.left_mem t).1 hownerQ
      exact ⟨t.1, htLeft, htOwnerQ⟩
    have hxpRoof : x ∈ Gamma.roof
        (C.ladder.frontier R.later.stage) := by
      change x ∈ (nativeCapturedGeometry R).outerRoof
      exact T.nativeIntervalReference_vertices_subset_capturedRoof
        ⟨p, hpRight.1, hxp⟩
    have hxLeft : x ∈ (E.leftPrefix t).support := by
      apply DWeb.KappaLadder.Deferred.limitComponent_support_inter_roof_subset_prefix
        C.legal R.later.stage hownerQ (E.left_mem t).1 hleftExt
      refine ⟨?_, hxpRoof⟩
      rw [← howners]
      exact hxpOwnerP
    have hxInter : x ∈ (E.leftPrefix t).support ∩
        (E.toSegmentRealization.segment t).support := ⟨hxLeft, hxq⟩
    rw [E.prefix_inter t] at hxInter
    have hxt : x = t.1 := by
      exact (Set.mem_singleton_iff.mp hxInter).trans (E.left_finish t)
    constructor
    · apply T.nativeWholeOwnerInterval_meetsOnlyAtTerminal p
        (Or.inr hpRight) x hxp
      rw [hxt]
      exact T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset
        t.2.1
    · change (E.toSegmentRealization.segment t).start = x
      exact (E.toSegmentRealization.segment_start t).trans hxt.symm

/-- The honest partial advance: splice precisely those old-row terminals
which remain outside the new closed carrier.  Closed terminals are left
unchanged. -/
noncomputable def nativeWholeOwnerPartialAdvance
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hcomponent : T.nativeWholeOwnerComponent ⊆ R'.closedSet) :
    Set Gamma.DPath :=
  Gamma.star
    (T.nativeWholeOwnerOutsideTerminalFamily_starCompatible
      R' hlater hcomponent)

/-- The exact old-terminal block left unmatched by the partial advance. -/
def nativeWholeOwnerClosedTerminals
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed') : Set V :=
  Gamma.terminalFrontier T.nativeWholeOwnerInterval ∩ R'.closedSet

/-- The unmatched terminal block remains `kappa`-bounded. -/
theorem nativeWholeOwnerClosedTerminals_card_le
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed') :
    # (T.nativeWholeOwnerClosedTerminals R') ≤ kappa := by
  exact (Cardinal.mk_subtype_mono Set.inter_subset_right).trans R'.card_le

theorem nativeWholeOwnerPartialAdvance_isWarp
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hcomponent : T.nativeWholeOwnerComponent ⊆ R'.closedSet) :
    Gamma.IsWarp
      (T.nativeWholeOwnerPartialAdvance R' hlater hcomponent) := by
  apply Gamma.isWarp_star
    T.nativeWholeOwnerInterval_isLinkageBetween.isWarp
    (T.nativeWholeOwnerOutsideTerminalFamily_isLinkageBetween
      R' hlater).isWarp

theorem nativeWholeOwnerPartialAdvance_finiteCharacter
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hcomponent : T.nativeWholeOwnerComponent ⊆ R'.closedSet) :
    Gamma.HasFiniteCharacter
      (T.nativeWholeOwnerPartialAdvance R' hlater hcomponent) := by
  apply SliceSpliceSource.hasFiniteCharacter_star
    T.nativeWholeOwnerInterval_isLinkageBetween.finiteCharacter
    (T.nativeWholeOwnerOutsideTerminalFamily_isLinkageBetween
      R' hlater).finiteCharacter

theorem nativeWholeOwnerPartialAdvance_initialSet
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hcomponent : T.nativeWholeOwnerComponent ⊆ R'.closedSet) :
    Gamma.initialSet
        (T.nativeWholeOwnerPartialAdvance R' hlater hcomponent) =
      (nativeCapturedGeometry R).oldSlice := by
  rw [nativeWholeOwnerPartialAdvance,
    SliceSpliceSource.initialSet_star_eq,
    T.nativeWholeOwnerInterval_isLinkageBetween.initialSet_eq]

/-- A closed old terminal is deliberately not spliced: no member of the
outside continuation family starts there, so the old finite path remains
literally exposed in the partial star. -/
theorem nativeWholeOwnerClosedTerminals_subset_partialAdvance_terminalFrontier
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hcomponent : T.nativeWholeOwnerComponent ⊆ R'.closedSet) :
    T.nativeWholeOwnerClosedTerminals R' ⊆
      Gamma.terminalFrontier
        (T.nativeWholeOwnerPartialAdvance R' hlater hcomponent) := by
  let E := T.nativeWholeOwnerOutsideTerminalRealization R' hlater
  let U := SliceSegmentCore.segmentFamily E.toSegmentRealization
  let hcompat := T.nativeWholeOwnerOutsideTerminalFamily_starCompatible
    R' hlater hcomponent
  rintro t ⟨htOld, htClosed⟩
  obtain ⟨p, hpRow, hpTerminal⟩ := htOld
  rcases p with f | ray
  · let old : T.nativeWholeOwnerInterval := ⟨Sum.inl f, hpRow⟩
    have hnomatch : ¬ ∃ q ∈ U, q.initial = f.finish := by
      rintro ⟨q, hqU, hqstart⟩
      have hqInitial : q.initial ∈ Gamma.initialSet U := ⟨q, hqU, rfl⟩
      rw [(T.nativeWholeOwnerOutsideTerminalFamily_isLinkageBetween
        R' hlater).initialSet_eq] at hqInitial
      have hfinish : f.finish = t := Option.some.inj hpTerminal
      have htOutside : t ∈ T.nativeWholeOwnerOutsideTerminals R' := by
        rw [← hfinish, ← hqstart]
        exact hqInitial
      exact htOutside.2 htClosed
    refine ⟨Gamma.starPath hcompat old, ⟨old, rfl⟩, ?_⟩
    dsimp only [old]
    simp only [DWeb.starPath]
    rw [dif_neg hnomatch]
    exact hpTerminal
  · simp only [DWeb.terminal?, Path.terminal?] at hpTerminal
    cases hpTerminal

/-- Every terminal after the partial advance is either on the genuinely
later frontier or is an old terminal absorbed by the new closure. -/
theorem nativeWholeOwnerPartialAdvance_terminalFrontier_subset
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hcomponent : T.nativeWholeOwnerComponent ⊆ R'.closedSet) :
    Gamma.terminalFrontier
        (T.nativeWholeOwnerPartialAdvance R' hlater hcomponent) ⊆
      C.ladder.frontier R'.later.stage ∪
        (Gamma.terminalFrontier T.nativeWholeOwnerInterval ∩
          R'.closedSet) := by
  let E := T.nativeWholeOwnerOutsideTerminalRealization R' hlater
  let U := SliceSegmentCore.segmentFamily E.toSegmentRealization
  let hcompat := T.nativeWholeOwnerOutsideTerminalFamily_starCompatible
    R' hlater hcomponent
  change Gamma.terminalFrontier (Gamma.star hcompat) ⊆ _
  rintro v ⟨r, ⟨p, rfl⟩, hrv⟩
  rcases p with ⟨p, hpRow⟩
  rcases p with f | ray
  · by_cases hmatch : ∃ q ∈ U, q.initial = f.finish
    · left
      simp only [DWeb.starPath] at hrv
      rw [dif_pos hmatch] at hrv
      let q := Classical.choose hmatch
      have hqU : q ∈ U := (Classical.choose_spec hmatch).1
      have hqstart : q.initial = f.finish :=
        (Classical.choose_spec hmatch).2
      have hinter : f.support ∩ q.support ⊆ {f.finish} := by
        intro x hx
        have hx' := hcompat (.inl f) hpRow q hqU x hx.1 hx.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
      have hqTerminal : q.terminal? = some v := by
        have happend := Path.terminal?_appendFinite f q hqstart hinter
        rw [← happend]
        dsimp only [q]
        exact hrv
      exact (T.nativeWholeOwnerOutsideTerminalFamily_isLinkageBetween
        R' hlater).terminalFrontier_subset ⟨q, hqU, hqTerminal⟩
    · right
      have hvfinish : v = f.finish := by
        simp only [DWeb.starPath] at hrv
        rw [dif_neg hmatch] at hrv
        exact Option.some.inj hrv.symm
      have hvOld : v ∈ Gamma.terminalFrontier
          T.nativeWholeOwnerInterval := by
        exact ⟨Sum.inl f, hpRow, congrArg some hvfinish.symm⟩
      refine ⟨hvOld, ?_⟩
      by_contra hvClosed
      have hvOutside : v ∈ T.nativeWholeOwnerOutsideTerminals R' :=
        ⟨hvOld, hvClosed⟩
      have hvInitial : v ∈ Gamma.initialSet U := by
        rw [(T.nativeWholeOwnerOutsideTerminalFamily_isLinkageBetween
          R' hlater).initialSet_eq]
        exact hvOutside
      obtain ⟨q, hqU, hqInitial⟩ := hvInitial
      apply hmatch
      exact ⟨q, hqU, hqInitial.trans hvfinish⟩
  · simp only [DWeb.starPath, DWeb.terminal?, Path.terminal?] at hrv
    cases hrv

/-- Concrete combined handoff: whole-owner reclosure produces a strictly
later partial advance with an exact source set, a controlled terminal
boundary, and only a `kappa`-bounded closed-terminal remainder. -/
theorem exists_reclosed_wholeOwnerPartialAdvance
    (T : NativePostClosureIntervalTransaction C seed z R) :
    ∃ R' : LimitClosure C T.nativeWholeOwnerClosingSeed,
      ∃ hlater : R.later.stage < R'.later.stage,
      ∃ hcomponent : T.nativeWholeOwnerComponent ⊆ R'.closedSet,
        R.closedSet ⊆ R'.closedSet ∧
        ClosedUnderPaths Gamma T.nativeWholeOwnerInterval R'.closedSet ∧
        Gamma.IsWarp
          (T.nativeWholeOwnerPartialAdvance R' hlater hcomponent) ∧
        Gamma.HasFiniteCharacter
          (T.nativeWholeOwnerPartialAdvance R' hlater hcomponent) ∧
        Gamma.initialSet
            (T.nativeWholeOwnerPartialAdvance R' hlater hcomponent) =
          (nativeCapturedGeometry R).oldSlice ∧
        Gamma.terminalFrontier
            (T.nativeWholeOwnerPartialAdvance R' hlater hcomponent) ⊆
          C.ladder.frontier R'.later.stage ∪
            T.nativeWholeOwnerClosedTerminals R' ∧
        #(T.nativeWholeOwnerClosedTerminals R') ≤ kappa ∧
        T.nativeWholeOwnerClosedTerminals R' ⊆
          Gamma.terminalFrontier
            (T.nativeWholeOwnerPartialAdvance R' hlater hcomponent) := by
  obtain ⟨R', hlater, hRsub, hcomponent, hclosed,
      _hfront, _hpath, _htail⟩ := T.exists_reclosed_wholeOwnerTransaction
  refine ⟨R', hlater, hcomponent, hRsub, hclosed,
    T.nativeWholeOwnerPartialAdvance_isWarp R' hlater hcomponent,
    T.nativeWholeOwnerPartialAdvance_finiteCharacter R' hlater hcomponent,
    T.nativeWholeOwnerPartialAdvance_initialSet R' hlater hcomponent,
    ?_, T.nativeWholeOwnerClosedTerminals_card_le R',
    T.nativeWholeOwnerClosedTerminals_subset_partialAdvance_terminalFrontier
      R' hlater hcomponent⟩
  simpa only [nativeWholeOwnerClosedTerminals] using
    T.nativeWholeOwnerPartialAdvance_terminalFrontier_subset
      R' hlater hcomponent

#print axioms
  NativePostClosureIntervalTransaction.nativeWholeOwnerOutsideTerminalFamily_starCompatible
#print axioms NativePostClosureIntervalTransaction.nativeWholeOwnerPartialAdvance_isWarp
#print axioms
  NativePostClosureIntervalTransaction.nativeWholeOwnerClosedTerminals_subset_partialAdvance_terminalFrontier
#print axioms
  NativePostClosureIntervalTransaction.nativeWholeOwnerPartialAdvance_terminalFrontier_subset
#print axioms
  NativePostClosureIntervalTransaction.exists_reclosed_wholeOwnerPartialAdvance

end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
