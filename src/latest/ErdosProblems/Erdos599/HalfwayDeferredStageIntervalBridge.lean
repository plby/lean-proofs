/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredRegularGeometry
import ErdosProblems.Erdos599.RegularSliceSurvivors
import ErdosProblems.Erdos599.SliceStageIntervalBridge

/-!
# Retyping survivor intervals for the deferred ladder

The canonical Section 9 ladder uses deferred bookkeeping.  Its geometric
laws are the same as those used to retype a literal interval in an essential
quotient stage, but it must not be cast to `IsSplitLegal`: deferred validity
does not imply validity for the larger legacy availability family.

This file repeats only the bookkeeping-free retyping argument with
`HalfwayGeometry`.  It supplies the missing honest bridge between the
canonical club geometry and the old-to-new interval transaction.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace DeferredStageInterval

open DirectedPath
open DWeb.KappaLadder.Deferred
open SliceCandidate

universe u

variable {V : Type u}

private theorem exists_essentialFinitePath_finish
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa}
    (hroof : L.RoofsSourceAtStages) {a : Ladder.Stage kappa}
    {x : V} (hx : x ∈ L.frontier a) :
    ∃ p : FinitePath Gamma.graph,
      (Sum.inl p : Gamma.DPath) ∈
        Gamma.essentialWarpPart (L.warpAt a) ∧ p.finish = x := by
  obtain ⟨p, hp, hterm⟩ :=
    Gamma.exists_essentialWarpPart_terminal_of_mem_quotientEssentialPart_source
      (hroof (Ladder.Stage.toExtended a)) hx
  rcases p with p | r
  · exact ⟨p, hp, Option.some.inj hterm⟩
  · simp at hterm

/-- Exact successor arrows of a deferred-legal ladder still extend every
old component; bookkeeping validity is irrelevant to this projection. -/
theorem successorExtensions
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    (a : Ladder.Stage kappa) (p : Gamma.DPath) (hp : p ∈ L.warpAt a) :
    ∃ q ∈ L.successorWarp a, Gamma.Extends p q := by
  obtain ⟨q, hq, _⟩ := (hL.exactSuccessorArrows a).1.1 p hp
  exact ⟨q, hq.1.1, hq.2.extends⟩

/-- Deferred ladder growth between arbitrary ordered ordinary stages. -/
theorem warpAt_grows_of_le
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta) :
    Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta) := by
  have hall : ∀ b : Ordinal.{u}, ∀ hb : b < kappa.ord,
      ∀ delta : Ladder.Stage kappa, delta.1 ≤ b →
        Gamma.LadderGrows (L.warpAt delta) (L.warpAt ⟨b, hb⟩) := by
    intro b
    induction b using Ordinal.lt_wf.induction with
    | h b ih =>
      intro hb delta hdeltaBeta
      let beta : Ladder.Stage kappa := ⟨b, hb⟩
      change Gamma.LadderGrows (L.warpAt delta) (L.warpAt beta)
      rcases Ordinal.zero_or_succ_or_isSuccLimit beta.1 with
          hzero | ⟨previous, hprevious⟩ | hlimit
      · have hdelta : delta = beta := by
          apply Subtype.ext
          change b = 0 at hzero
          change delta.1 = b
          apply le_antisymm hdeltaBeta
          rw [hzero]
          exact bot_le
        subst delta
        exact Gamma.ladderGrows_refl _
      · by_cases heq : delta = beta
        · subst delta
          exact Gamma.ladderGrows_refl _
        · have hdeltaLt : delta < beta := lt_of_le_of_ne hdeltaBeta heq
          have hpreviousLt : previous < beta.1 := by
            rw [← hprevious]
            exact Order.lt_succ previous
          let previousStage : Ladder.Stage kappa :=
            ⟨previous, hpreviousLt.trans beta.2⟩
          have hdeltaPrevious : delta ≤ previousStage := by
            apply Subtype.coe_le_coe.1
            change delta.1 < b at hdeltaLt
            change Order.succ previous = b at hprevious
            rw [← hprevious] at hdeltaLt
            exact Order.lt_succ_iff.mp hdeltaLt
          have hgrowsPrevious : Gamma.LadderGrows
              (L.warpAt delta) (L.warpAt previousStage) :=
            ih previous hpreviousLt previousStage.2 delta hdeltaPrevious
          have hgrowsSuccessor : Gamma.LadderGrows
              (L.warpAt previousStage) (L.warpAt beta) := by
            intro p hp
            obtain ⟨q, hq, hpq⟩ :=
              successorExtensions hL previousStage p hp
            refine ⟨q, ?_, hpq⟩
            change q ∈ L.accumulated (Ladder.Stage.toExtended beta)
            change q ∈ L.accumulated
              (Ladder.Stage.succExtended previousStage) at hq
            have hstage : Ladder.Stage.toExtended beta =
                Ladder.Stage.succExtended previousStage := by
              apply Subtype.ext
              change b = previous + 1
              exact hprevious.symm
            rwa [hstage]
          exact DWeb.LadderGrows.trans (G := Gamma)
            hgrowsPrevious hgrowsSuccessor
      · by_cases heq : delta = beta
        · subst delta
          exact Gamma.ladderGrows_refl _
        · have hdeltaLt : delta < beta := lt_of_le_of_ne hdeltaBeta heq
          let deltaBelow : Set.Iio beta.1 := ⟨delta.1, hdeltaLt⟩
          intro p hp
          exact hL.limitStages.grows_to_limit
            (Ladder.Stage.toExtended beta) hlimit deltaBelow p hp
  exact hall beta.1 beta.2 delta hdeltaBeta

/-- The raw strict roof deleted at the earlier stage is disjoint from every
later deferred frontier. -/
theorem rawStrictRoof_disjoint_laterFrontier
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} (hL : HalfwayGeometry L)
    {delta beta : Ladder.Stage kappa} (hdeltaBeta : delta ≤ beta) :
    Disjoint
      (Gamma.strictRoof (Gamma.terminalFrontier (L.warpAt delta)))
      (L.frontier beta) := by
  have heq : Gamma.strictRoof
        (Gamma.terminalFrontier (L.warpAt delta)) =
      Gamma.strictRoof (L.frontier delta) := by
    rw [L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages delta, Gamma.strictRoof_essential]
  rw [heq]
  rcases hdeltaBeta.lt_or_eq with hlt | rfl
  · exact hL.strictFrontierChronology hlt
  · have h := Gamma.disjoint_strictRoof_essential (L.frontier delta)
    rwa [hL.frontiersEssential delta] at h

/-- Raw-old-frontier purity of a deferred survivor interval. -/
theorem StageIntervalRealization.segment_rawSource_pure
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) (x : S) :
    (R.toSegmentRealization.segment x).support ∩
        Gamma.terminalFrontier (L.warpAt delta) =
      {(R.toSegmentRealization.segment x).start} := by
  apply Set.Subset.antisymm
  · rintro y ⟨hySegment, hyFrontier⟩
    obtain ⟨p, hpDelta, hpy⟩ := hyFrontier
    obtain ⟨q, hqBeta, hpq⟩ :=
      warpAt_grows_of_le hL hdeltaBeta p hpDelta
    let hstart : DirectedPath.Path.initial
        (Sum.inl (R.toSegmentRealization.segment x) : Gamma.DPath) =
          (R.leftPrefix x).finish := by
      change (R.toSegmentRealization.segment x).start =
        (R.leftPrefix x).finish
      exact R.toSegmentRealization.segment_start x |>.trans
        (R.left_finish x).symm
    let hinter : (R.leftPrefix x).support ∩
        DirectedPath.Path.support
          (Sum.inl (R.toSegmentRealization.segment x) : Gamma.DPath) ⊆
          {(R.leftPrefix x).finish} := by
      change (R.leftPrefix x).support ∩
        (R.toSegmentRealization.segment x).support ⊆
          {(R.leftPrefix x).finish}
      exact (R.prefix_inter x).subset
    let appended : Gamma.DPath :=
      DirectedPath.Path.appendFinite (R.leftPrefix x)
        (.inl (R.toSegmentRealization.segment x)) hstart hinter
    have happended : appended =
        (Sum.inl (R.rightPrefix x) : Gamma.DPath) := by
      simpa only [appended] using R.append_eq x
    have hyRight : y ∈ (R.rightPrefix x).support := by
      have hyAppend : y ∈ appended.support := by
        dsimp only [appended]
        rw [DirectedPath.Path.support_appendFinite]
        exact Or.inr hySegment
      rw [happended] at hyAppend
      exact hyAppend
    have hyQ : y ∈ q.support :=
      Gamma.support_mono_of_extends hpq
        (Gamma.terminal_mem_support hpy)
    have hqRight : q = (Sum.inl (R.rightPrefix x) : Gamma.DPath) := by
      by_contra hne
      exact Set.disjoint_left.1
        (hL.warpStages (Ladder.Stage.toExtended beta)
          hqBeta (R.right_mem x).1 hne) hyQ hyRight
    have hpInitial : p.initial = (R.leftPrefix x).start := by
      calc
        p.initial = q.initial := Gamma.extends_initial hpq
        _ = (R.rightPrefix x).start :=
          congrArg DirectedPath.Path.initial hqRight
        _ = (R.leftPrefix x).start := by
          calc
            (R.rightPrefix x).start = appended.initial :=
              congrArg DirectedPath.Path.initial happended.symm
            _ = (R.leftPrefix x).start :=
              DirectedPath.Path.initial_appendFinite _ _ _ _
    have hpLeft : p =
        (Sum.inl (R.leftPrefix x) : Gamma.DPath) := by
      apply DWeb.IsWarp.eq_of_initial_eq Gamma
        (hL.warpStages (Ladder.Stage.toExtended delta))
        hpDelta (R.left_mem x).1
      exact hpInitial
    apply Set.mem_singleton_iff.mpr
    calc
      y = (R.leftPrefix x).finish := by
        have h := hpy
        rw [hpLeft] at h
        exact Option.some.inj h |>.symm
      _ = x.1 := R.left_finish x
      _ = (R.toSegmentRealization.segment x).start :=
        (R.toSegmentRealization.segment_start x).symm
  · intro y hy
    have hyStart : y = (R.toSegmentRealization.segment x).start :=
      Set.mem_singleton_iff.mp hy
    subst y
    refine ⟨(R.toSegmentRealization.segment x).start_mem_support, ?_⟩
    rw [R.toSegmentRealization.segment_start x, ← R.left_finish x]
    exact ⟨Sum.inl (R.leftPrefix x), (R.left_mem x).1, rfl⟩

/-- The terminal of a deferred stage interval is reachable in the earlier
essential quotient stage. -/
theorem StageIntervalRealization.segment_finish_stageReachable
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) (x : S) :
    (R.toSegmentRealization.segment x).finish ∈
      (L.stageWeb delta).reachableToTarget := by
  let T := Gamma.terminalFrontier (L.warpAt delta)
  let p := R.toSegmentRealization.segment x
  have hpure : p.support ∩ T = {p.start} :=
    DeferredStageInterval.StageIntervalRealization.segment_rawSource_pure
      R hL hdeltaBeta x
  have hstartFrontier : p.start ∈ L.frontier delta := by
    rw [R.toSegmentRealization.segment_start x]
    exact R.toSegmentRealization.source_subset x.2
  have hfinishFrontier : p.finish ∈ L.frontier beta :=
    R.toSegmentRealization.segment_finish_mem x
  have hfinishNotStrict : p.finish ∉ Gamma.strictRoof T :=
    fun h ↦ Set.disjoint_left.1
      (rawStrictRoof_disjoint_laterFrontier hL hdeltaBeta)
      h hfinishFrontier
  by_cases hfinishT : p.finish ∈ T
  · have hfinishEq : p.finish = p.start := by
      apply Set.mem_singleton_iff.mp
      rw [← hpure]
      exact ⟨p.finish_mem_support, hfinishT⟩
    rw [hfinishEq]
    exact (Gamma.quotient T).mem_essentialPart_reachableToTarget_of_mem'
      hstartFrontier.2
  · have hfinishNotRoof : p.finish ∉ Gamma.roof T := by
      intro hroof
      apply hfinishNotStrict
      exact ⟨hroof, fun hessential ↦ hfinishT
        (Gamma.essential_subset T hessential)⟩
    exact SliceCandidate.mem_stageWeb_reachable_of_not_mem_rawRoof
      L delta hfinishNotRoof

/-- Quotient admissibility of a deferred survivor interval. -/
theorem StageIntervalRealization.stageSegment_admissible
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) (x : S) :
    Gamma.PathQuotientAdmissible
      (Gamma.terminalFrontier (L.warpAt delta))
      (Sum.inl (R.toSegmentRealization.segment x)) := by
  let T := Gamma.terminalFrontier (L.warpAt delta)
  let p := R.toSegmentRealization.segment x
  have hpure : p.support ∩ T = {p.start} :=
    DeferredStageInterval.StageIntervalRealization.segment_rawSource_pure
      R hL hdeltaBeta x
  have hstartFrontier : p.start ∈ L.frontier delta := by
    rw [R.toSegmentRealization.segment_start x]
    exact R.toSegmentRealization.source_subset x.2
  have hstartEssential : p.start ∈ Gamma.essential T := by
    rw [← L.frontier_eq_essential_terminalFrontier
      hL.roofsSourceAtStages delta]
    exact hstartFrontier
  have hfinishFrontier : p.finish ∈ L.frontier beta :=
    R.toSegmentRealization.segment_finish_mem x
  have hfinishNotStrict : p.finish ∉ Gamma.strictRoof T :=
    fun h ↦ Set.disjoint_left.1
      (rawStrictRoof_disjoint_laterFrontier hL hdeltaBeta)
      h hfinishFrontier
  exact finitePath_pathQuotientAdmissible_of_sourcePure Gamma p
    hpure hstartEssential hfinishNotStrict

/-- Retype one literal interval in the earlier deferred essential quotient
stage. -/
noncomputable def StageIntervalRealization.stageSegment
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) (x : S) :
    (L.stageWeb delta).DPath := by
  let T := Gamma.terminalFrontier (L.warpAt delta)
  let p := R.toSegmentRealization.segment x
  let hadm : Gamma.PathQuotientAdmissible T (Sum.inl p) :=
    DeferredStageInterval.StageIntervalRealization.stageSegment_admissible
      R hL hdeltaBeta x
  let q : DirectedPath.FinitePath (Gamma.quotient T).graph :=
    Gamma.restrictFinitePathToQuotient T p hadm.1 hadm.2
  have hfinishReach : q.finish ∈
      (Gamma.quotient T).reachableToTarget := by
    change p.finish ∈ (Gamma.quotient T).reachableToTarget
    exact SliceCandidate.reachableToTarget_essentialPart_subset
      (Gamma.quotient T)
      (DeferredStageInterval.StageIntervalRealization.segment_finish_stageReachable
        R hL hdeltaBeta x)
  have hreach : DirectedPath.Path.support
      (Sum.inl q : (Gamma.quotient T).DPath) ⊆
      (Gamma.quotient T).reachableToTarget := by
    change q.support ⊆ (Gamma.quotient T).reachableToTarget
    exact finitePath_support_subset_reachable_of_finish
      (Gamma.quotient T) q hfinishReach
  exact (Gamma.quotient T).restrictEssentialPartPath (.inl q) hreach

/-- Ambient lifting recovers the literal interval, including its walk and
edge order. -/
@[simp] theorem StageIntervalRealization.liftStagePath_stageSegment
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) (x : S) :
    L.liftStagePath delta
        (DeferredStageInterval.StageIntervalRealization.stageSegment
          R hL hdeltaBeta x) =
      (Sum.inl (R.toSegmentRealization.segment x) : Gamma.DPath) := by
  let T := Gamma.terminalFrontier (L.warpAt delta)
  let p := R.toSegmentRealization.segment x
  let hadm : Gamma.PathQuotientAdmissible T (Sum.inl p) :=
    DeferredStageInterval.StageIntervalRealization.stageSegment_admissible
      R hL hdeltaBeta x
  let q : DirectedPath.FinitePath (Gamma.quotient T).graph :=
    Gamma.restrictFinitePathToQuotient T p hadm.1 hadm.2
  have hfinishReach : q.finish ∈
      (Gamma.quotient T).reachableToTarget := by
    change p.finish ∈ (Gamma.quotient T).reachableToTarget
    exact SliceCandidate.reachableToTarget_essentialPart_subset
      (Gamma.quotient T)
      (DeferredStageInterval.StageIntervalRealization.segment_finish_stageReachable
        R hL hdeltaBeta x)
  have hreach : DirectedPath.Path.support
      (Sum.inl q : (Gamma.quotient T).DPath) ⊆
      (Gamma.quotient T).reachableToTarget := by
    change q.support ⊆ (Gamma.quotient T).reachableToTarget
    exact finitePath_support_subset_reachable_of_finish
      (Gamma.quotient T) q hfinishReach
  change Gamma.liftQuotientPath T
      ((Gamma.quotient T).liftEssentialPartPath
        ((Gamma.quotient T).restrictEssentialPartPath (.inl q) hreach)) =
    (Sum.inl p : Gamma.DPath)
  rw [liftEssentialPartPath_restrictEssentialPartPath]
  unfold DWeb.liftQuotientPath
  apply congrArg Sum.inl
  exact lift_restrictFinitePathToQuotient Gamma T p hadm.1 hadm.2

@[simp] theorem StageIntervalRealization.support_stageSegment
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) (x : S) :
    (DeferredStageInterval.StageIntervalRealization.stageSegment
      R hL hdeltaBeta x).support =
      (R.toSegmentRealization.segment x).support := by
  simp only [DeferredStageInterval.StageIntervalRealization.stageSegment,
    DWeb.KappaLadder.stageWeb, DWeb.stageWebOf,
    DWeb.support_restrictEssentialPartPath]
  change (Gamma.restrictFinitePathToQuotient _
    (R.toSegmentRealization.segment x) _ _).support =
      (R.toSegmentRealization.segment x).support
  exact Gamma.support_restrictFinitePathToQuotient _ _
    (DeferredStageInterval.StageIntervalRealization.stageSegment_admissible
      R hL hdeltaBeta x).1
    (DeferredStageInterval.StageIntervalRealization.stageSegment_admissible
      R hL hdeltaBeta x).2

@[simp] theorem StageIntervalRealization.initial_stageSegment
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) (x : S) :
    (DeferredStageInterval.StageIntervalRealization.stageSegment
      R hL hdeltaBeta x).initial = x.1 := by
  simp only [DeferredStageInterval.StageIntervalRealization.stageSegment,
    DWeb.KappaLadder.stageWeb, DWeb.stageWebOf,
    initial_restrictEssentialPartPath]
  exact R.toSegmentRealization.segment_start x

@[simp] theorem StageIntervalRealization.terminal_stageSegment
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) (x : S) :
    (L.stageWeb delta).terminal?
        (DeferredStageInterval.StageIntervalRealization.stageSegment
          R hL hdeltaBeta x) =
      some (R.toSegmentRealization.segment x).finish := by
  simp only [DeferredStageInterval.StageIntervalRealization.stageSegment,
    DWeb.KappaLadder.stageWeb, DWeb.stageWebOf,
    terminal_restrictEssentialPartPath]
  rfl

/-- The family of all retyped deferred intervals. -/
noncomputable def StageIntervalRealization.stageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) :
    Set (L.stageWeb delta).DPath :=
  Set.range fun x : S ↦
    DeferredStageInterval.StageIntervalRealization.stageSegment
      R hL hdeltaBeta x

/-- Family-level exactness after ambient lifting. -/
@[simp] theorem StageIntervalRealization.liftStageFamily_stageFamily
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) :
    SliceSegmentCore.liftStageFamily L delta
        (DeferredStageInterval.StageIntervalRealization.stageFamily
          R hL hdeltaBeta) =
      SliceSegmentCore.segmentFamily R.toSegmentRealization := by
  ext p
  constructor
  · rintro ⟨q, ⟨x, rfl⟩, rfl⟩
    rw [DeferredStageInterval.StageIntervalRealization.liftStagePath_stageSegment]
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨DeferredStageInterval.StageIntervalRealization.stageSegment
      R hL hdeltaBeta x, ⟨x, rfl⟩, ?_⟩
    exact DeferredStageInterval.StageIntervalRealization.liftStagePath_stageSegment
      R hL hdeltaBeta x

theorem StageIntervalRealization.stageSegment_finite
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) (x : S) :
    ∃ q : DirectedPath.FinitePath (L.stageWeb delta).graph,
      DeferredStageInterval.StageIntervalRealization.stageSegment
        R hL hdeltaBeta x = Sum.inl q := by
  unfold DeferredStageInterval.StageIntervalRealization.stageSegment
  exact ⟨_, rfl⟩

/-- The retyped deferred intervals form the exact linkage between the
chosen survivor sources and the later frontier. -/
theorem StageIntervalRealization.stageFamily_isLinkageBetween
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) :
    IsLinkageBetween (L.stageWeb delta) S (L.frontier beta)
      (DeferredStageInterval.StageIntervalRealization.stageFamily
        R hL hdeltaBeta) := by
  let F := DeferredStageInterval.StageIntervalRealization.stageFamily
    R hL hdeltaBeta
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨x, rfl⟩ q ⟨y, rfl⟩ hpq
    have hxy : x ≠ y := by
      intro h
      subst y
      exact hpq rfl
    have hambient := SliceSegmentCore.segmentFamily_isWarp
      (hL.warpStages (Ladder.Stage.toExtended beta))
      R.toSegmentRealization
    have hdis := hambient
      (show (Sum.inl (R.toSegmentRealization.segment x) : Gamma.DPath) ∈
          SliceSegmentCore.segmentFamily R.toSegmentRealization from
        ⟨x, rfl⟩)
      (show (Sum.inl (R.toSegmentRealization.segment y) : Gamma.DPath) ∈
          SliceSegmentCore.segmentFamily R.toSegmentRealization from
        ⟨y, rfl⟩)
      (by
        intro h
        apply hxy
        apply Subtype.ext
        have hi := congrArg DirectedPath.Path.initial h
        exact (R.toSegmentRealization.segment_start x).symm.trans
          (hi.trans (R.toSegmentRealization.segment_start y)))
    change Disjoint
      (DeferredStageInterval.StageIntervalRealization.stageSegment
        R hL hdeltaBeta x).support
      (DeferredStageInterval.StageIntervalRealization.stageSegment
        R hL hdeltaBeta y).support
    rw [DeferredStageInterval.StageIntervalRealization.support_stageSegment,
      DeferredStageInterval.StageIntervalRealization.support_stageSegment]
    exact hdis
  · rintro p ⟨x, rfl⟩
    exact DeferredStageInterval.StageIntervalRealization.stageSegment_finite
      R hL hdeltaBeta x
  · ext v
    constructor
    · rintro ⟨p, ⟨x, rfl⟩, hp⟩
      rw [DeferredStageInterval.StageIntervalRealization.initial_stageSegment]
        at hp
      exact hp ▸ x.2
    · intro hv
      let x : S := ⟨v, hv⟩
      exact ⟨DeferredStageInterval.StageIntervalRealization.stageSegment
          R hL hdeltaBeta x, ⟨x, rfl⟩,
        DeferredStageInterval.StageIntervalRealization.initial_stageSegment
          R hL hdeltaBeta x⟩
  · rintro v ⟨p, ⟨x, rfl⟩, hp⟩
    rw [DeferredStageInterval.StageIntervalRealization.terminal_stageSegment]
      at hp
    exact Option.some.inj hp ▸
      R.toSegmentRealization.segment_finish_mem x
  · rintro p ⟨x, rfl⟩
    obtain ⟨q, hq⟩ :=
      DeferredStageInterval.StageIntervalRealization.stageSegment_finite
        R hL hdeltaBeta x
    have hsupport : q.support =
        (R.toSegmentRealization.segment x).support := by
      calc
        q.support = DirectedPath.Path.support
            (Sum.inl q : (L.stageWeb delta).DPath) := rfl
        _ = (DeferredStageInterval.StageIntervalRealization.stageSegment
              R hL hdeltaBeta x).support :=
          congrArg DirectedPath.Path.support hq.symm
        _ = _ :=
          DeferredStageInterval.StageIntervalRealization.support_stageSegment
            R hL hdeltaBeta x
    have hstart : q.start =
        (R.toSegmentRealization.segment x).start := by
      calc
        q.start = DirectedPath.Path.initial
            (Sum.inl q : (L.stageWeb delta).DPath) := rfl
        _ = (DeferredStageInterval.StageIntervalRealization.stageSegment
              R hL hdeltaBeta x).initial :=
          congrArg DirectedPath.Path.initial hq.symm
        _ = x.1 :=
          DeferredStageInterval.StageIntervalRealization.initial_stageSegment
            R hL hdeltaBeta x
        _ = (R.toSegmentRealization.segment x).start :=
          (R.toSegmentRealization.segment_start x).symm
    have hfinish : q.finish =
        (R.toSegmentRealization.segment x).finish := by
      apply Option.some.inj
      calc
        some q.finish = (L.stageWeb delta).terminal?
            (Sum.inl q : (L.stageWeb delta).DPath) := rfl
        _ = (L.stageWeb delta).terminal?
            (DeferredStageInterval.StageIntervalRealization.stageSegment
              R hL hdeltaBeta x) :=
          congrArg (L.stageWeb delta).terminal? hq.symm
        _ = _ :=
          DeferredStageInterval.StageIntervalRealization.terminal_stageSegment
            R hL hdeltaBeta x
    refine ⟨q, hq, ?_, ?_⟩
    · rw [hsupport, hstart, hfinish]
      ext v
      constructor
      · rintro ⟨hvSupport, hv⟩
        have hv' : v ∈ (R.toSegmentRealization.segment x).support ∩
            (L.frontier delta ∪ L.frontier beta) :=
          ⟨hvSupport, hv.elim
            (fun h ↦ Or.inl (R.toSegmentRealization.source_subset h))
            Or.inr⟩
        rw [R.toSegmentRealization.segment_endpoints x] at hv'
        exact hv'
      · intro hv
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · exact ⟨(R.toSegmentRealization.segment x).start_mem_support,
            Or.inl (R.toSegmentRealization.segment_start x ▸ x.2)⟩
        · exact ⟨(R.toSegmentRealization.segment x).finish_mem_support,
            Or.inr (R.toSegmentRealization.segment_finish_mem x)⟩
    · rw [hsupport, hstart]
      ext v
      constructor
      · rintro ⟨hvSupport, hvS⟩
        have hv' : v ∈ (R.toSegmentRealization.segment x).support ∩
            L.frontier delta :=
          ⟨hvSupport, R.toSegmentRealization.source_subset hvS⟩
        rw [R.toSegmentRealization.segment_source x] at hv'
        exact hv'
      · intro hv
        have hvstart : v = (R.toSegmentRealization.segment x).start := by
          simpa only [Set.mem_singleton_iff] using hv
        subst v
        exact ⟨(R.toSegmentRealization.segment x).start_mem_support,
          R.toSegmentRealization.segment_start x ▸ x.2⟩

/-- Later-frontier purity of an arbitrary retained stage realization. -/
theorem StageIntervalRealization.segment_frontier_beta
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (x : S) :
    (R.toSegmentRealization.segment x).support ∩ L.frontier beta =
      {(R.toSegmentRealization.segment x).finish} := by
  apply Set.Subset.antisymm
  · rintro y ⟨hySegment, hyFrontier⟩
    obtain ⟨p, hp, hpfinish⟩ :=
      exists_essentialFinitePath_finish hL.roofsSourceAtStages hyFrontier
    have hyRight : y ∈ (R.rightPrefix x).support := by
      let hstart : DirectedPath.Path.initial
          (Sum.inl (R.toSegmentRealization.segment x) : Gamma.DPath) =
            (R.leftPrefix x).finish := by
        change (R.toSegmentRealization.segment x).start =
          (R.leftPrefix x).finish
        exact (R.toSegmentRealization.segment_start x).trans
          (R.left_finish x).symm
      let hinter : (R.leftPrefix x).support ∩
          DirectedPath.Path.support
            (Sum.inl (R.toSegmentRealization.segment x) : Gamma.DPath) ⊆
            {(R.leftPrefix x).finish} := by
        change (R.leftPrefix x).support ∩
          (R.toSegmentRealization.segment x).support ⊆
            {(R.leftPrefix x).finish}
        exact (R.prefix_inter x).subset
      let appended : Gamma.DPath :=
        DirectedPath.Path.appendFinite (R.leftPrefix x)
          (.inl (R.toSegmentRealization.segment x)) hstart hinter
      have happended : appended =
          (Sum.inl (R.rightPrefix x) : Gamma.DPath) := by
        simpa only [appended] using R.append_eq x
      have hyAppend : y ∈ appended.support := by
        dsimp only [appended]
        rw [DirectedPath.Path.support_appendFinite]
        exact Or.inr hySegment
      rw [happended] at hyAppend
      exact hyAppend
    have hpright : p = R.rightPrefix x := by
      by_contra hne
      have hdis := hL.warpStages (Ladder.Stage.toExtended beta)
        hp.1 (R.right_mem x).1 (fun h ↦ hne (Sum.inl.inj h))
      exact Set.disjoint_left.1 hdis
        (hpfinish.symm ▸ p.finish_mem_support) hyRight
    apply Set.mem_singleton_iff.mpr
    calc
      y = p.finish := hpfinish.symm
      _ = (R.rightPrefix x).finish := congrArg FinitePath.finish hpright
      _ = (R.toSegmentRealization.segment x).finish := R.right_finish x
  · intro y hy
    have hy' : y = (R.toSegmentRealization.segment x).finish :=
      Set.mem_singleton_iff.mp hy
    subst y
    exact ⟨(R.toSegmentRealization.segment x).finish_mem_support,
      R.toSegmentRealization.segment_finish_mem x⟩

/-- Deferred interval families meet the later frontier only at their
terminal. -/
theorem StageIntervalRealization.stageFamily_meetsOnlyAtTerminal
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    {L : Gamma.KappaLadder kappa} {delta beta : Ladder.Stage kappa}
    {S : Set V} (R : StageIntervalRealization L delta beta S)
    (hL : HalfwayGeometry L) (hdeltaBeta : delta ≤ beta) :
    SliceSpliceSource.MeetsOnlyAtTerminal (L.stageWeb delta)
      (DeferredStageInterval.StageIntervalRealization.stageFamily
        R hL hdeltaBeta) (L.frontier beta) := by
  intro p hp x hxp hxBeta
  obtain ⟨s, rfl⟩ := hp
  have hxAmbient : x ∈
      (R.toSegmentRealization.segment s).support := by
    simpa only [
      DeferredStageInterval.StageIntervalRealization.support_stageSegment]
      using hxp
  have hxFinish : x =
      (R.toSegmentRealization.segment s).finish := by
    apply Set.mem_singleton_iff.mp
    rw [← DeferredStageInterval.StageIntervalRealization.segment_frontier_beta
      R hL s]
    exact ⟨hxAmbient, hxBeta⟩
  rw [DeferredStageInterval.StageIntervalRealization.terminal_stageSegment]
  exact congrArg some hxFinish.symm

#print axioms warpAt_grows_of_le
#print axioms StageIntervalRealization.stageSegment
#print axioms StageIntervalRealization.liftStagePath_stageSegment
#print axioms StageIntervalRealization.stageFamily_isLinkageBetween
#print axioms StageIntervalRealization.stageFamily_meetsOnlyAtTerminal

end DeferredStageInterval
end CardinalInduction
end Erdos599
