/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeWholeOwnerTerminalSplice

/-!
# Advancing every surviving terminal of the native whole-owner row

Closedness is not an obstruction to advancing a terminal which genuinely
survives to the later stage.  The canonical survivor intervals can be
spliced simultaneously with the whole normalized row: a contact lies on
the later interval's limiting owner, and the old row lies below the old
frontier, so the no-late-entry prefix theorem puts the contact on the old
prefix.  Prefix/segment intersection then forces the common endpoint.

Consequently only nonsurviving old terminals remain.  They lie in the new
closed set, form a `kappa`-bounded set, and the whole limiting owner through
each one is an inessential component of the new stage warp.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.Alternating
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

/-- Old normalized-row terminals which survive to the strictly later
stage, independently of whether they are in the new closed set. -/
def nativeWholeOwnerSurvivingTerminals
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed') : Set V :=
  Gamma.terminalFrontier T.nativeWholeOwnerInterval ∩
    survivorSources Gamma C.ladder R.later.stage R'.later.stage

/-- The exact residual terminal block after advancing every survivor. -/
def nativeWholeOwnerNonsurvivingTerminals
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed') : Set V :=
  Gamma.terminalFrontier T.nativeWholeOwnerInterval \
    survivorSources Gamma C.ladder R.later.stage R'.later.stage

/-- Any old terminal whose limiting owner hits the later frontier is a
survivor source. -/
theorem terminal_mem_survivorSources_of_limitOwner_hitting_later
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {t : V} (htOld : t ∈ C.ladder.frontier R.later.stage)
    {p : Gamma.DPath} (hp : p ∈ C.ladder.limitWarp)
    (htp : t ∈ p.support)
    (hpLater : p ∈ C.limitReferenceAtFrontier R'.later.stage) :
    t ∈ survivorSources Gamma C.ladder
      R.later.stage R'.later.stage := by
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

/-- Canonical simultaneous intervals for all surviving old terminals. -/
noncomputable def nativeWholeOwnerSurvivingTerminalRealization
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    StageIntervalRealization C.ladder R.later.stage R'.later.stage
      (T.nativeWholeOwnerSurvivingTerminals R') :=
  stageIntervalRealizationOfSubset_of_geometry
    (fun _ ht ↦ ht.2)
    C.legal.roofsSourceAtStages C.legal.warpStages
    (warpAt_grows_of_le C.legal hlater.le)

theorem nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    IsLinkageBetween Gamma (T.nativeWholeOwnerSurvivingTerminals R')
      (C.ladder.frontier R'.later.stage)
      (SliceSegmentCore.segmentFamily
        (T.nativeWholeOwnerSurvivingTerminalRealization
          R' hlater).toSegmentRealization) := by
  exact SliceSegmentCore.segmentFamily_isLinkageBetween
    (C.legal.warpStages (Ladder.Stage.toExtended R'.later.stage))
    (T.nativeWholeOwnerSurvivingTerminalRealization
      R' hlater).toSegmentRealization

/-- Every surviving-terminal interval is star-compatible with the entire
normalized row.  No closed-set avoidance is needed. -/
theorem nativeWholeOwnerSurvivingTerminalFamily_starCompatible
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    Gamma.StarCompatible T.nativeWholeOwnerInterval
      (SliceSegmentCore.segmentFamily
        (T.nativeWholeOwnerSurvivingTerminalRealization
          R' hlater).toSegmentRealization) := by
  let E := T.nativeWholeOwnerSurvivingTerminalRealization R' hlater
  intro p hp q hq x hxp hxq
  obtain ⟨t, rfl⟩ := hq
  have hlimit : Order.IsSuccLimit (succ kappa).ord :=
    Cardinal.isSuccLimit_ord C.legal.regular.aleph0_le
  obtain ⟨owner, howner, hrightExt⟩ :=
    C.legal.limitStages.grows_to_limit
      (Ladder.finalStage (succ kappa)) hlimit
      ⟨R'.later.stage.1, R'.later.stage.2⟩
      (Sum.inl (E.rightPrefix t) : Gamma.DPath)
      (E.right_mem t).1
  have hxOwner : x ∈ owner.support :=
    Gamma.support_mono_of_extends hrightExt
      ((E.segment_subpath t).1 hxq)
  have htLeft : t.1 ∈ (E.leftPrefix t).support := by
    rw [← E.left_finish t]
    exact (E.leftPrefix t).finish_mem_support
  have htOwner : t.1 ∈ owner.support := by
    have htRight : t.1 ∈ (E.rightPrefix t).support := by
      have htSegment : t.1 ∈
          (E.toSegmentRealization.segment t).support := by
        rw [← E.toSegmentRealization.segment_start t]
        exact (E.toSegmentRealization.segment t).start_mem_support
      exact (E.segment_subpath t).1 htSegment
    exact Gamma.support_mono_of_extends hrightExt htRight
  have hleftExt : Gamma.Extends
      (Sum.inl (E.leftPrefix t) : Gamma.DPath) owner := by
    apply C.legal.extends_limitWarp_of_stage_intersects
      (E.left_mem t).1 howner
    exact ⟨t.1, htLeft, htOwner⟩
  have hxpRoof : x ∈ Gamma.roof
      (C.ladder.frontier R.later.stage) := by
    change x ∈ (nativeCapturedGeometry R).outerRoof
    exact T.nativeWholeOwnerInterval_vertices_subset_capturedRoof
      ⟨p, hp, hxp⟩
  have hxLeft : x ∈ (E.leftPrefix t).support := by
    exact DWeb.KappaLadder.Deferred.limitComponent_support_inter_roof_subset_prefix
      C.legal R.later.stage howner (E.left_mem t).1 hleftExt
        ⟨hxOwner, hxpRoof⟩
  have hxInter : x ∈ (E.leftPrefix t).support ∩
      (E.toSegmentRealization.segment t).support := ⟨hxLeft, hxq⟩
  rw [E.prefix_inter t] at hxInter
  have hxt : x = t.1 :=
    (Set.mem_singleton_iff.mp hxInter).trans (E.left_finish t)
  constructor
  · apply T.nativeWholeOwnerInterval_meetsOnlyAtTerminal p hp x hxp
    rw [hxt]
    exact T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset
      t.2.1
  · change (E.toSegmentRealization.segment t).start = x
    exact (E.toSegmentRealization.segment_start t).trans hxt.symm

/-- Splice the normalized row simultaneously along every surviving old
terminal. -/
noncomputable def nativeWholeOwnerSurvivorAdvance
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) : Set Gamma.DPath :=
  Gamma.star
    (T.nativeWholeOwnerSurvivingTerminalFamily_starCompatible R' hlater)

theorem nativeWholeOwnerSurvivorAdvance_isWarp
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    Gamma.IsWarp (T.nativeWholeOwnerSurvivorAdvance R' hlater) := by
  apply Gamma.isWarp_star
    T.nativeWholeOwnerInterval_isLinkageBetween.isWarp
    (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
      R' hlater).isWarp

theorem nativeWholeOwnerSurvivorAdvance_finiteCharacter
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    Gamma.HasFiniteCharacter (T.nativeWholeOwnerSurvivorAdvance R' hlater) := by
  apply SliceSpliceSource.hasFiniteCharacter_star
    T.nativeWholeOwnerInterval_isLinkageBetween.finiteCharacter
    (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
      R' hlater).finiteCharacter

theorem nativeWholeOwnerSurvivorAdvance_initialSet
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    Gamma.initialSet (T.nativeWholeOwnerSurvivorAdvance R' hlater) =
      (nativeCapturedGeometry R).oldSlice := by
  rw [nativeWholeOwnerSurvivorAdvance,
    SliceSpliceSource.initialSet_star_eq,
    T.nativeWholeOwnerInterval_isLinkageBetween.initialSet_eq]

/-- Every nonsurviving old terminal is absorbed by the new closure. -/
theorem nativeWholeOwnerNonsurvivingTerminals_subset_closedSet
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    T.nativeWholeOwnerNonsurvivingTerminals R' ⊆ R'.closedSet := by
  intro t ht
  by_contra htClosed
  apply ht.2
  exact T.nativeWholeOwnerOutsideTerminals_subset_survivorSources
    R' hlater ⟨ht.1, htClosed⟩

theorem nativeWholeOwnerNonsurvivingTerminals_card_le
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    #(T.nativeWholeOwnerNonsurvivingTerminals R') ≤ kappa :=
  (Cardinal.mk_subtype_mono
    (T.nativeWholeOwnerNonsurvivingTerminals_subset_closedSet
      R' hlater)).trans R'.card_le

/-- Nonsurviving terminals are exactly the old terminals deliberately left
unmatched, hence remain exposed in the survivor advance. -/
theorem nativeWholeOwnerNonsurvivingTerminals_subset_survivorAdvance_terminalFrontier
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    T.nativeWholeOwnerNonsurvivingTerminals R' ⊆
      Gamma.terminalFrontier
        (T.nativeWholeOwnerSurvivorAdvance R' hlater) := by
  let E := T.nativeWholeOwnerSurvivingTerminalRealization R' hlater
  let U := SliceSegmentCore.segmentFamily E.toSegmentRealization
  let hcompat := T.nativeWholeOwnerSurvivingTerminalFamily_starCompatible
    R' hlater
  rintro t ⟨htOld, htNotSurvivor⟩
  obtain ⟨p, hpRow, hpTerminal⟩ := htOld
  rcases p with f | ray
  · let old : T.nativeWholeOwnerInterval := ⟨Sum.inl f, hpRow⟩
    have hnomatch : ¬ ∃ q ∈ U, q.initial = f.finish := by
      rintro ⟨q, hqU, hqstart⟩
      have hqInitial : q.initial ∈ Gamma.initialSet U := ⟨q, hqU, rfl⟩
      rw [(T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
        R' hlater).initialSet_eq] at hqInitial
      have hfinish : f.finish = t := Option.some.inj hpTerminal
      apply htNotSurvivor
      have : t ∈ T.nativeWholeOwnerSurvivingTerminals R' := by
        rw [← hfinish, ← hqstart]
        exact hqInitial
      exact this.2
    refine ⟨Gamma.starPath hcompat old, ⟨old, rfl⟩, ?_⟩
    dsimp only [old]
    simp only [DWeb.starPath]
    rw [dif_neg hnomatch]
    exact hpTerminal
  · simp only [DWeb.terminal?, Path.terminal?] at hpTerminal
    cases hpTerminal

/-- The survivor advance exposes only new-frontier terminals and the exact
nonsurviving old-terminal block. -/
theorem nativeWholeOwnerSurvivorAdvance_terminalFrontier_subset
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) :
    Gamma.terminalFrontier
        (T.nativeWholeOwnerSurvivorAdvance R' hlater) ⊆
      C.ladder.frontier R'.later.stage ∪
        T.nativeWholeOwnerNonsurvivingTerminals R' := by
  let E := T.nativeWholeOwnerSurvivingTerminalRealization R' hlater
  let U := SliceSegmentCore.segmentFamily E.toSegmentRealization
  let hcompat := T.nativeWholeOwnerSurvivingTerminalFamily_starCompatible
    R' hlater
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
      exact (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
        R' hlater).terminalFrontier_subset ⟨q, hqU, hqTerminal⟩
    · right
      have hvfinish : v = f.finish := by
        simp only [DWeb.starPath] at hrv
        rw [dif_neg hmatch] at hrv
        exact Option.some.inj hrv.symm
      have hvOld : v ∈ Gamma.terminalFrontier
          T.nativeWholeOwnerInterval :=
        ⟨Sum.inl f, hpRow, congrArg some hvfinish.symm⟩
      refine ⟨hvOld, ?_⟩
      intro hvSurvivor
      have hvSource : v ∈ T.nativeWholeOwnerSurvivingTerminals R' :=
        ⟨hvOld, hvSurvivor⟩
      have hvInitial : v ∈ Gamma.initialSet U := by
        rw [(T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
          R' hlater).initialSet_eq]
        exact hvSource
      obtain ⟨q, hqU, hqInitial⟩ := hvInitial
      apply hmatch
      exact ⟨q, hqU, hqInitial.trans hvfinish⟩
  · simp only [DWeb.starPath, DWeb.terminal?, Path.terminal?] at hrv
    cases hrv

/-- The owner through a residual nonsurviving terminal is necessarily an
inessential component of the new stage warp.  The finite-persistent branch
would hit the new frontier and hence make the terminal a survivor. -/
theorem nonsurvivingTerminal_exists_inessential_limitOwner
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {t : V} (ht : t ∈ T.nativeWholeOwnerNonsurvivingTerminals R') :
    ∃ p ∈ C.ladder.limitWarp, t ∈ p.support ∧
      p ∈ Gamma.inessentialPaths
        (C.ladder.warpAt R'.later.stage) := by
  have htClosed : t ∈ R'.closedSet :=
    T.nativeWholeOwnerNonsurvivingTerminals_subset_closedSet R' hlater ht
  obtain ⟨p, hp, htp, hpClosed, hpClass⟩ :=
    T.closedTerminal_owner_classification R' ht.1 htClosed
  refine ⟨p, hp, htp, ?_⟩
  rcases hpClass with hpFinite | hpInessential
  · obtain ⟨f, rfl, hfPersistent, hfClosed⟩ := hpFinite
    exfalso
    apply ht.2
    apply T.terminal_mem_survivorSources_of_limitOwner_hitting_later
      R' hlater
      (T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset
        ht.1)
      hp htp
    refine ⟨hp, f.finish, f.finish_mem_support, ?_⟩
    have hpair : f.finish ∈ R'.closedSet ∩ C.persistent :=
      ⟨hfClosed f.finish_mem_support, hfPersistent⟩
    rw [← R'.frontier_inter] at hpair
    exact hpair.2
  · exact hpInessential

#print axioms
  NativePostClosureIntervalTransaction.nativeWholeOwnerSurvivingTerminalFamily_starCompatible
#print axioms
  NativePostClosureIntervalTransaction.nativeWholeOwnerSurvivorAdvance_terminalFrontier_subset
#print axioms
  NativePostClosureIntervalTransaction.nativeWholeOwnerNonsurvivingTerminals_card_le
#print axioms
  NativePostClosureIntervalTransaction.nonsurvivingTerminal_exists_inessential_limitOwner

end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
