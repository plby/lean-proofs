/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeWholeOwnerResidualTarget
import ErdosProblems.Erdos599.SingularSafeCarrierCardinal

/-!
# The honest residual/survivor partial star

A small residual target linkage need not be disjoint from every canonical
survivor interval beyond the old roof.  This file removes exactly the
survivor intervals which meet that target linkage.  Their initial set is
still `kappa`-bounded.  The remaining survivor intervals and the target
linkage form a genuine warp, and their union is star-compatible with the
whole normalized old row.

No claim is made that the colliding survivor sources can be added to the
target linkage without changing it.  Iterating that replacement requires a
protected deletion or an equivalent joint-selection invariant.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.RegularSliceSurvivors
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

/-- Exact terminal accounting for a partially covered source star.  New
terminals are exposed by the continuation family; the only old terminals
which remain exposed are those not used as continuation initials. -/
theorem terminalFrontier_star_eq_union_unmatched
    {W U : Set Gamma.DPath}
    (hWfinite : Gamma.HasFiniteCharacter W)
    (hUwarp : Gamma.IsWarp U)
    (hcompat : Gamma.StarCompatible W U)
    (hstart : Gamma.initialSet U ⊆ Gamma.terminalFrontier W) :
    Gamma.terminalFrontier (Gamma.star hcompat) =
      Gamma.terminalFrontier U ∪
        (Gamma.terminalFrontier W \ Gamma.initialSet U) := by
  apply Set.Subset.antisymm
  · rintro x ⟨r, ⟨p, rfl⟩, hrx⟩
    rcases p with ⟨p, hpW⟩
    obtain ⟨f, rfl⟩ := hWfinite hpW
    by_cases hmatch : ∃ q ∈ U, q.initial = f.finish
    · left
      simp only [DWeb.starPath] at hrx
      rw [dif_pos hmatch] at hrx
      let q := Classical.choose hmatch
      have hqU : q ∈ U := (Classical.choose_spec hmatch).1
      have hqstart : q.initial = f.finish :=
        (Classical.choose_spec hmatch).2
      have hinter : f.support ∩ q.support ⊆ {f.finish} := by
        intro y hy
        have hy' := hcompat (.inl f) hpW q hqU y hy.1 hy.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hy'.1).symm
      refine ⟨q, hqU, ?_⟩
      have hterm := DirectedPath.Path.terminal?_appendFinite
        f q hqstart hinter
      change DirectedPath.Path.terminal? q = some x
      rw [← hterm]
      dsimp only [q]
      exact hrx
    · right
      simp only [DWeb.starPath] at hrx
      rw [dif_neg hmatch] at hrx
      refine ⟨⟨.inl f, hpW, hrx⟩, ?_⟩
      intro hxInitial
      obtain ⟨q, hqU, hqx⟩ := hxInitial
      apply hmatch
      exact ⟨q, hqU, hqx.trans (Option.some.inj hrx).symm⟩
  · rintro x (hxU | hxOld)
    · obtain ⟨q, hqU, hqx⟩ := hxU
      have hqInitial : q.initial ∈ Gamma.initialSet U := ⟨q, hqU, rfl⟩
      obtain ⟨p, hpW, hpterm⟩ := hstart hqInitial
      obtain ⟨f, rfl⟩ := hWfinite hpW
      have hqStart : q.initial = f.finish :=
        (Option.some.inj hpterm).symm
      have hmatch : ∃ r ∈ U, r.initial = f.finish :=
        ⟨q, hqU, hqStart⟩
      let chosen : Gamma.DPath := Classical.choose hmatch
      have hchosenU : chosen ∈ U := (Classical.choose_spec hmatch).1
      have hchosenInitial : chosen.initial = f.finish :=
        (Classical.choose_spec hmatch).2
      have hchosenEq : chosen = q :=
        DWeb.IsWarp.eq_of_initial_eq Gamma hUwarp hchosenU hqU
          (hchosenInitial.trans hqStart.symm)
      let old : W := ⟨(.inl f : Gamma.DPath), hpW⟩
      refine ⟨Gamma.starPath hcompat old, ⟨old, rfl⟩, ?_⟩
      dsimp only [old, DWeb.starPath]
      rw [dif_pos hmatch]
      have hinter : f.support ∩ chosen.support ⊆ {f.finish} := by
        intro y hy
        have hy' := hcompat (.inl f) hpW chosen hchosenU y hy.1 hy.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hy'.1).symm
      exact (DirectedPath.Path.terminal?_appendFinite
        f chosen hchosenInitial hinter).trans (hchosenEq ▸ hqx)
    · obtain ⟨⟨p, hpW, hpx⟩, hxNotStart⟩ := hxOld
      obtain ⟨f, rfl⟩ := hWfinite hpW
      have hnomatch : ¬ ∃ q ∈ U, q.initial = f.finish := by
        rintro ⟨q, hqU, hqstart⟩
        apply hxNotStart
        exact ⟨q, hqU, hqstart.trans (Option.some.inj hpx)⟩
      let old : W := ⟨.inl f, hpW⟩
      refine ⟨Gamma.starPath hcompat old, ⟨old, rfl⟩, ?_⟩
      dsimp only [old, DWeb.starPath]
      rw [dif_neg hnomatch]
      exact hpx

/-- Survivor intervals which meet the carrier of a chosen residual target
linkage. -/
def nativeWholeOwnerCollidingSurvivorFamily
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (P : Set Gamma.DPath) : Set Gamma.DPath :=
  {q | q ∈ SliceSegmentCore.segmentFamily
      (T.nativeWholeOwnerSurvivingTerminalRealization R' hlater).toSegmentRealization ∧
    ¬ Disjoint q.support (Gamma.vertexSet P)}

/-- The old survivor sources whose canonical intervals collide with `P`. -/
def nativeWholeOwnerCollidingSurvivorSources
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (P : Set Gamma.DPath) : Set V :=
  Gamma.initialSet
    (T.nativeWholeOwnerCollidingSurvivorFamily R' hlater P)

/-- The canonical survivor intervals left after deleting precisely the
intervals which meet `P`. -/
def nativeWholeOwnerNoncollidingSurvivorFamily
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (P : Set Gamma.DPath) : Set Gamma.DPath :=
  SliceSegmentCore.segmentFamily
      (T.nativeWholeOwnerSurvivingTerminalRealization R' hlater).toSegmentRealization \
    T.nativeWholeOwnerCollidingSurvivorFamily R' hlater P

theorem nativeWholeOwnerCollidingSurvivorFamily_subset
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (P : Set Gamma.DPath) :
    T.nativeWholeOwnerCollidingSurvivorFamily R' hlater P ⊆
      SliceSegmentCore.segmentFamily
        (T.nativeWholeOwnerSurvivingTerminalRealization
          R' hlater).toSegmentRealization := by
  intro q hq
  exact hq.1

/-- The collision source set is bounded by `kappa`: the target linkage has
at most `kappa` vertices, and disjoint survivor intervals inject into any
set which they meet. -/
theorem nativeWholeOwnerCollidingSurvivorSources_card_le
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {P : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma
      (T.nativeWholeOwnerNonsurvivingTerminals R') Gamma.target P) :
    #(T.nativeWholeOwnerCollidingSurvivorSources R' hlater P) ≤ kappa := by
  let E := SliceSegmentCore.segmentFamily
    (T.nativeWholeOwnerSurvivingTerminalRealization
      R' hlater).toSegmentRealization
  let Bad := T.nativeWholeOwnerCollidingSurvivorFamily R' hlater P
  have hBad : #Bad ≤ #(Gamma.vertexSet P) := by
    change #({q | q ∈ E ∧ ¬ Disjoint q.support (Gamma.vertexSet P)} :
      Set Gamma.DPath) ≤ #(Gamma.vertexSet P)
    exact Gamma.mk_pathsMeeting_le E (Gamma.vertexSet P)
      (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
        R' hlater).isWarp
  have hPvertices : #(Gamma.vertexSet P) ≤ kappa := by
    refine (SingularSafeCarrierCardinal.mk_vertexSet_le_max_initial_aleph0
      hP).trans ?_
    exact max_le
      (T.nativeWholeOwnerNonsurvivingTerminals_card_le R' hlater)
      C.capacity_infinite
  exact (RegularProtectedAmbientRebuild.mk_initialSet_le_family Gamma Bad).trans
    (hBad.trans hPvertices)

theorem nativeWholeOwnerCollidingSurvivorSources_subset_surviving
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (P : Set Gamma.DPath) :
    T.nativeWholeOwnerCollidingSurvivorSources R' hlater P ⊆
      T.nativeWholeOwnerSurvivingTerminals R' := by
  rintro x ⟨q, hqBad, rfl⟩
  rw [← (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
    R' hlater).initialSet_eq]
  exact ⟨q, hqBad.1, rfl⟩

/-- By construction, every retained survivor interval avoids the target
linkage carrier. -/
theorem nativeWholeOwnerNoncollidingSurvivorFamily_disjoint
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (P : Set Gamma.DPath) :
    Disjoint
      (Gamma.vertexSet
        (T.nativeWholeOwnerNoncollidingSurvivorFamily R' hlater P))
      (Gamma.vertexSet P) := by
  rw [Set.disjoint_left]
  intro x hxGood hxP
  obtain ⟨q, hqGood, hxq⟩ := hxGood
  apply hqGood.2
  exact ⟨hqGood.1, Set.not_disjoint_iff.2 ⟨x, hxq, hxP⟩⟩

theorem nativeWholeOwnerNoncollidingSurvivorFamily_initialSet
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (P : Set Gamma.DPath) :
    Gamma.initialSet
        (T.nativeWholeOwnerNoncollidingSurvivorFamily R' hlater P) =
      T.nativeWholeOwnerSurvivingTerminals R' \
        T.nativeWholeOwnerCollidingSurvivorSources R' hlater P := by
  let E := SliceSegmentCore.segmentFamily
    (T.nativeWholeOwnerSurvivingTerminalRealization
      R' hlater).toSegmentRealization
  let Bad := T.nativeWholeOwnerCollidingSurvivorFamily R' hlater P
  have hEwarp : Gamma.IsWarp E :=
    (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
      R' hlater).isWarp
  apply Set.Subset.antisymm
  · rintro x ⟨q, hqGood, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
        R' hlater).initialSet_eq]
      exact ⟨q, hqGood.1, rfl⟩
    · rintro ⟨r, hrBad, hrstart⟩
      have hqr : q = r := DWeb.IsWarp.eq_of_initial_eq Gamma hEwarp
        hqGood.1 hrBad.1 hrstart.symm
      exact hqGood.2 (hqr ▸ hrBad)
  · rintro x ⟨hxSurviving, hxNotBad⟩
    have hxInitial : x ∈ Gamma.initialSet E := by
      rw [(T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
        R' hlater).initialSet_eq]
      exact hxSurviving
    obtain ⟨q, hqE, hqstart⟩ := hxInitial
    refine ⟨q, ⟨hqE, ?_⟩, hqstart⟩
    intro hqBad
    exact hxNotBad ⟨q, hqBad, hqstart⟩

/-- The residual target linkage together with all noncolliding survivor
intervals. -/
def nativeWholeOwnerResidualPartialContinuation
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (P : Set Gamma.DPath) : Set Gamma.DPath :=
  P ∪ T.nativeWholeOwnerNoncollidingSurvivorFamily R' hlater P

theorem nativeWholeOwnerResidualPartialContinuation_isWarp
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {P : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma
      (T.nativeWholeOwnerNonsurvivingTerminals R') Gamma.target P) :
    Gamma.IsWarp
      (T.nativeWholeOwnerResidualPartialContinuation R' hlater P) := by
  let E := SliceSegmentCore.segmentFamily
    (T.nativeWholeOwnerSurvivingTerminalRealization
      R' hlater).toSegmentRealization
  let Good := T.nativeWholeOwnerNoncollidingSurvivorFamily R' hlater P
  have hE : Gamma.IsWarp E :=
    (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
      R' hlater).isWarp
  have hdisjoint : Disjoint (Gamma.vertexSet Good) (Gamma.vertexSet P) :=
    T.nativeWholeOwnerNoncollidingSurvivorFamily_disjoint R' hlater P
  intro p hp q hq hpq
  rcases hp with hpP | hpGood <;> rcases hq with hqP | hqGood
  · exact hP.isWarp hpP hqP hpq
  · change Disjoint p.support q.support
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.1 hdisjoint
      ⟨q, hqGood, hxq⟩ ⟨p, hpP, hxp⟩
  · change Disjoint p.support q.support
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.1 hdisjoint
      ⟨p, hpGood, hxp⟩ ⟨q, hqP, hxq⟩
  · exact hE hpGood.1 hqGood.1 hpq

theorem nativeWholeOwnerResidualPartialContinuation_finiteCharacter
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {P : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma
      (T.nativeWholeOwnerNonsurvivingTerminals R') Gamma.target P) :
    Gamma.HasFiniteCharacter
      (T.nativeWholeOwnerResidualPartialContinuation R' hlater P) := by
  intro q hq
  rcases hq with hqP | hqGood
  · exact hP.finiteCharacter hqP
  · exact (T.nativeWholeOwnerSurvivingTerminalFamily_isLinkageBetween
      R' hlater).finiteCharacter hqGood.1

theorem nativeWholeOwnerResidualPartialContinuation_initialSet
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {P : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma
      (T.nativeWholeOwnerNonsurvivingTerminals R') Gamma.target P) :
    Gamma.initialSet
        (T.nativeWholeOwnerResidualPartialContinuation R' hlater P) =
      Gamma.terminalFrontier T.nativeWholeOwnerInterval \
        T.nativeWholeOwnerCollidingSurvivorSources R' hlater P := by
  rw [nativeWholeOwnerResidualPartialContinuation,
    Gamma.initialSet_union, hP.initialSet_eq,
    T.nativeWholeOwnerNoncollidingSurvivorFamily_initialSet R' hlater P]
  have hbad := T.nativeWholeOwnerCollidingSurvivorSources_subset_surviving
    R' hlater P
  ext x
  constructor
  · rintro (hxResidual | ⟨hxSurviving, hxNotBad⟩)
    · exact ⟨hxResidual.1, fun hxBad ↦ hxResidual.2 (hbad hxBad).2⟩
    · exact ⟨hxSurviving.1, hxNotBad⟩
  · rintro ⟨hxOld, hxNotBad⟩
    by_cases hxSurvivor : x ∈ survivorSources Gamma C.ladder
        R.later.stage R'.later.stage
    · exact Or.inr ⟨⟨hxOld, hxSurvivor⟩, hxNotBad⟩
    · exact Or.inl ⟨hxOld, hxSurvivor⟩

theorem nativeWholeOwnerResidualPartialContinuation_starCompatible
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {P : Set Gamma.DPath}
    (hPcompat : Gamma.StarCompatible T.nativeWholeOwnerInterval P) :
    Gamma.StarCompatible T.nativeWholeOwnerInterval
      (T.nativeWholeOwnerResidualPartialContinuation R' hlater P) := by
  intro p hp q hq x hxp hxq
  rcases hq with hqP | hqGood
  · exact hPcompat p hp q hqP x hxp hxq
  · exact T.nativeWholeOwnerSurvivingTerminalFamily_starCompatible
      R' hlater p hp q hqGood.1 x hxp hxq

/-- The actual partial star: every residual terminal reaches the original
target, every noncolliding survivor reaches the later frontier, and only
the bounded collision-source block is deliberately left unmatched. -/
noncomputable def nativeWholeOwnerResidualPartialStar
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (P : Set Gamma.DPath)
    (hPcompat : Gamma.StarCompatible T.nativeWholeOwnerInterval P) :
    Set Gamma.DPath :=
  Gamma.star
    (T.nativeWholeOwnerResidualPartialContinuation_starCompatible
      R' hlater hPcompat)

theorem nativeWholeOwnerResidualPartialStar_isWarp
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {P : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma
      (T.nativeWholeOwnerNonsurvivingTerminals R') Gamma.target P)
    (hPcompat : Gamma.StarCompatible T.nativeWholeOwnerInterval P) :
    Gamma.IsWarp
      (T.nativeWholeOwnerResidualPartialStar R' hlater P hPcompat) := by
  apply Gamma.isWarp_star
    T.nativeWholeOwnerInterval_isLinkageBetween.isWarp
    (T.nativeWholeOwnerResidualPartialContinuation_isWarp R' hlater hP)

theorem nativeWholeOwnerResidualPartialStar_finiteCharacter
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {P : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma
      (T.nativeWholeOwnerNonsurvivingTerminals R') Gamma.target P)
    (hPcompat : Gamma.StarCompatible T.nativeWholeOwnerInterval P) :
    Gamma.HasFiniteCharacter
      (T.nativeWholeOwnerResidualPartialStar R' hlater P hPcompat) := by
  apply SliceSpliceSource.hasFiniteCharacter_star
    T.nativeWholeOwnerInterval_isLinkageBetween.finiteCharacter
    (T.nativeWholeOwnerResidualPartialContinuation_finiteCharacter
      R' hlater hP)

theorem nativeWholeOwnerResidualPartialStar_initialSet
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {P : Set Gamma.DPath}
    (hPcompat : Gamma.StarCompatible T.nativeWholeOwnerInterval P) :
    Gamma.initialSet
        (T.nativeWholeOwnerResidualPartialStar R' hlater P hPcompat) =
      (nativeCapturedGeometry R).oldSlice := by
  rw [nativeWholeOwnerResidualPartialStar,
    SliceSpliceSource.initialSet_star_eq,
    T.nativeWholeOwnerInterval_isLinkageBetween.initialSet_eq]

/-- Exact unresolved-terminal identity.  The partial star exposes the
continuation terminals together with exactly the colliding survivor
sources, and no other old terminals. -/
theorem nativeWholeOwnerResidualPartialStar_terminalFrontier
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    {P : Set Gamma.DPath}
    (hP : IsLinkageBetween Gamma
      (T.nativeWholeOwnerNonsurvivingTerminals R') Gamma.target P)
    (hPcompat : Gamma.StarCompatible T.nativeWholeOwnerInterval P) :
    Gamma.terminalFrontier
        (T.nativeWholeOwnerResidualPartialStar R' hlater P hPcompat) =
      Gamma.terminalFrontier
          (T.nativeWholeOwnerResidualPartialContinuation R' hlater P) ∪
        T.nativeWholeOwnerCollidingSurvivorSources R' hlater P := by
  let U := T.nativeWholeOwnerResidualPartialContinuation R' hlater P
  let hcompat :=
    T.nativeWholeOwnerResidualPartialContinuation_starCompatible
      R' hlater hPcompat
  have hUinitial : Gamma.initialSet U =
      Gamma.terminalFrontier T.nativeWholeOwnerInterval \
        T.nativeWholeOwnerCollidingSurvivorSources R' hlater P :=
    T.nativeWholeOwnerResidualPartialContinuation_initialSet
      R' hlater hP
  have hUstart : Gamma.initialSet U ⊆
      Gamma.terminalFrontier T.nativeWholeOwnerInterval := by
    rw [hUinitial]
    exact Set.sdiff_subset
  have hbase := terminalFrontier_star_eq_union_unmatched
    T.nativeWholeOwnerInterval_isLinkageBetween.finiteCharacter
    (T.nativeWholeOwnerResidualPartialContinuation_isWarp R' hlater hP)
    hcompat hUstart
  have hunmatched :
      Gamma.terminalFrontier T.nativeWholeOwnerInterval \
          Gamma.initialSet U =
        T.nativeWholeOwnerCollidingSurvivorSources R' hlater P := by
    rw [hUinitial]
    have hbad : T.nativeWholeOwnerCollidingSurvivorSources R' hlater P ⊆
        Gamma.terminalFrontier T.nativeWholeOwnerInterval :=
      (T.nativeWholeOwnerCollidingSurvivorSources_subset_surviving
        R' hlater P).trans Set.inter_subset_left
    ext x
    simp only [Set.mem_sdiff]
    constructor
    · rintro ⟨hxOld, hxNot⟩
      by_contra hxBad
      exact hxNot ⟨hxOld, hxBad⟩
    · intro hxBad
      exact ⟨hbad hxBad, fun hx ↦ hx.2 hxBad⟩
  simpa only [nativeWholeOwnerResidualPartialStar, U, hcompat,
    hunmatched] using hbase

/-- Fully assembled output from the corrected current-cardinal extension.
It retains the target linkage and its exact old-roof incidence, constructs
the partial star, and exposes the bounded collision block. -/
theorem exists_nativeWholeOwnerResidualPartialStar
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage)
    (hext :
      _root_.Erdos599.CardinalInduction.ProtectedCardinalAssembly.ExtensionThroughFor
        Gamma kappa) :
    ∃ (P W : Set Gamma.DPath)
        (hcompat : Gamma.StarCompatible T.nativeWholeOwnerInterval P),
      IsLinkageBetween Gamma
          (T.nativeWholeOwnerNonsurvivingTerminals R') Gamma.target P ∧
      Gamma.vertexSet P ∩ (nativeCapturedGeometry R).outerRoof =
          T.nativeWholeOwnerNonsurvivingTerminals R' ∧
      #(T.nativeWholeOwnerCollidingSurvivorSources R' hlater P) ≤ kappa ∧
      W = T.nativeWholeOwnerResidualPartialStar R' hlater P hcompat ∧
      Gamma.IsWarp W ∧ Gamma.HasFiniteCharacter W ∧
      Gamma.initialSet W = (nativeCapturedGeometry R).oldSlice := by
  obtain ⟨P, hP, hroof, hcompat⟩ :=
    T.exists_nativeWholeOwnerResidualTargetLinkage R' hlater hext
  let W := T.nativeWholeOwnerResidualPartialStar R' hlater P hcompat
  refine ⟨P, W, hcompat, hP, hroof,
    T.nativeWholeOwnerCollidingSurvivorSources_card_le R' hlater hP,
    rfl, ?_, ?_, ?_⟩
  · exact T.nativeWholeOwnerResidualPartialStar_isWarp
      R' hlater hP hcompat
  · exact T.nativeWholeOwnerResidualPartialStar_finiteCharacter
      R' hlater hP hcompat
  · exact T.nativeWholeOwnerResidualPartialStar_initialSet
      R' hlater hcompat

#print axioms
  NativePostClosureIntervalTransaction.nativeWholeOwnerCollidingSurvivorSources_card_le
#print axioms
  NativePostClosureIntervalTransaction.nativeWholeOwnerResidualPartialStar_isWarp
#print axioms
  NativePostClosureIntervalTransaction.nativeWholeOwnerResidualPartialStar_finiteCharacter
#print axioms
  NativePostClosureIntervalTransaction.exists_nativeWholeOwnerResidualPartialStar
#print axioms
  NativePostClosureIntervalTransaction.nativeWholeOwnerResidualPartialStar_terminalFrontier

end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
