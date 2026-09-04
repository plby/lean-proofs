/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularLimitIndices
import ErdosProblems.Erdos599.RegularOrdinaryThreadLimit
import ErdosProblems.Erdos599.DeferredLimitHitClosure
import ErdosProblems.Erdos599.DeferredLimitMiss
import ErdosProblems.Erdos599.DeferredRegularGeometry

/-!
# The limit-stage compiler for the regular slice recursion

At a limit recursion index we take the threadwise direct limit of all
earlier partial linkages.  The strengthened stage invariant gives the
source dichotomy needed for each thread: a completed member remains
completed, while an unfinished member is a literal accumulated-ladder
prefix.  Pending mavericks cannot survive cofinally, because every later
stage is required to resolve every earlier pending terminal.

The right coordinates of the earlier payloads form a strictly increasing
cofinal family.  Thus a thread made of literal ladder prefixes is itself a
member of the ladder warp at their supremum.  If it missed that frontier,
it would be an inessential component and hence a member of the final warp;
the directed-supremum closure of its hit stages then forces a hit at the
supremum, a contradiction.  This is the precise use of source Lemma 7.28.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace CardinalInduction
namespace SliceSpliceConstructor
namespace LocalConstruction

open SliceSpliceSource

universe u

variable {V : Type u}

/-- The valid history below a limit recursion index, regarded as a growing
chain of partial source linkages. -/
noncomputable def limitHistoryChain
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z)
    (hprevious : ∀ j (hji : j < i),
      SliceSplice.IsValidStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) :
    Gamma.GrowingWarpChain (Set.Iio i) where
  stage j := (previous j.1 j.2).family
  isWarp j := (hprevious j.1 j.2).isWarp
  grows := by
    intro j l hjl p hp
    rcases hjl.lt_or_eq with hjl | rfl
    · exact (hprevious l.1 l.2).extends_previous j.1 hjl p hp
    · exact ⟨p, hp, Gamma.extends_refl p⟩

@[simp]
theorem limitHistoryChain_stage
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z)
    (hprevious : ∀ j (hji : j < i),
      SliceSplice.IsValidStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) (j : Set.Iio i) :
    (limitHistoryChain previous hprevious).stage j =
      (previous j.1 j.2).family :=
  rfl

/-- On each source thread of a valid limit history, either some earlier
member has already reached the original target, or every member is a
literal ladder prefix.  The third `path_status` alternative cannot persist:
the immediately following recursion stage resolves it to the target. -/
theorem completed_or_all_stagePrefix
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa} (hi : Order.IsSuccLimit i.1)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z)
    (hprevious : ∀ j (hji : j < i),
      SliceSplice.IsValidStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji))
    (a : (limitHistoryChain previous hprevious).initialUnion) :
    (∃ j : Set.Iio i, ∃ p,
      p ∈ (limitHistoryChain previous hprevious).stage j ∧
      p.initial = a.1 ∧
      ∃ b ∈ Gamma.target, Gamma.terminal? p = some b) ∨
    ∀ j p, p ∈ (limitHistoryChain previous hprevious).stage j →
      p.initial = a.1 →
      SliceSplice.StagePrefix Gamma L
        (previousNextIndex previous j) p := by
  classical
  let C := limitHistoryChain previous hprevious
  by_cases hcompleted : ∃ j : Set.Iio i, ∃ p,
      p ∈ C.stage j ∧ p.initial = a.1 ∧
        ∃ b ∈ Gamma.target, Gamma.terminal? p = some b
  · exact Or.inl hcompleted
  · right
    intro j p hp hpinitial
    rcases (hprevious j.1 j.2).path_status p hp with
      hpTarget | hpPrefix | hpPending
    · exact (hcompleted ⟨j, p, hp, hpinitial, hpTarget⟩).elim
    · exact hpPrefix
    · have hsucc : Order.succ j.1.1 < i.1 := hi.succ_lt j.2
      let lStage : Ladder.Stage kappa :=
        ⟨Order.succ j.1.1, hsucc.trans i.2⟩
      let l : Set.Iio i := ⟨lStage, hsucc⟩
      have hjl : j.1 < l.1 := Order.lt_succ j.1.1
      obtain ⟨q, hq, hpq, b, hbTarget, hqterm⟩ :=
        (hprevious l.1 l.2).resolves_previous_pending
          j.1 hjl p hp hpPending
      have hqinitial : q.initial = a.1 :=
        (Gamma.extends_initial hpq).symm.trans hpinitial
      exact (hcompleted ⟨l, q, hq, hqinitial,
        b, hbTarget, hqterm⟩).elim

/-- A valid limit history has a genuine tight direct limit at the supremum
of its earlier right coordinates. -/
theorem exists_tight_limitFamily
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized)
    (hL : SpliceLadderGeometry Gamma L)
    (hDeferred : DWeb.KappaLadder.Deferred.IsDeferredLegal L)
    (hA : A ⊆ Gamma.source)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    {i : Ladder.Stage kappa} (hi : Order.IsSuccLimit i.1)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      SliceSplice.StagePayload Gamma L Sigma Z)
    (hprevious : ∀ j (hji : j < i),
      SliceSplice.IsValidStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji))
    (B : LimitIndexData Sigma i (previousNextIndex previous)) :
    let C := limitHistoryChain previous hprevious
    let W := C.limitPaths Gamma
    TightLinkageBetween Gamma A (L.frontier B.index) W ∧
      Gamma.vertexSet W ⊆ Z ∧
      Gamma.vertexSet W ⊆ Gamma.roof (L.frontier B.index) ∧
      (∀ j, Gamma.ForwardExtension (C.stage j) W) ∧
      (∀ p ∈ W,
        (∃ b ∈ Gamma.target, Gamma.terminal? p = some b) ∨
          SliceSplice.StagePrefix Gamma L B.index p) := by
  classical
  dsimp only
  let C := limitHistoryChain previous hprevious
  have : Nonempty (Set.Iio i) :=
    ⟨⟨⟨0, hi.bot_lt.trans i.2⟩, hi.bot_lt⟩⟩
  have htight : ∀ j,
      TightLinkageBetween Gamma A
        (L.frontier (previousNextIndex previous j)) (C.stage j) := by
    intro j
    exact ⟨(hprevious j.1 j.2).linkage,
      (hprevious j.1 j.2).meets_frontier_only_at_terminal⟩
  have hroof : ∀ j, Gamma.vertexSet (C.stage j) ⊆
      Gamma.roof (L.frontier (previousNextIndex previous j)) :=
    fun j ↦ (hprevious j.1 j.2).vertices_roof
  have hZ : ∀ j, Gamma.vertexSet (C.stage j) ⊆ Z :=
    fun j ↦ (hprevious j.1 j.2).vertices_closed
  have hthreads : ∀ a : C.initialUnion,
      (L.frontier B.index ∩ (C.threadLimit Gamma a).support).Nonempty := by
    intro a
    rcases completed_or_all_stagePrefix hi previous hprevious a with
      hcompleted | hprefix
    · obtain ⟨j, p, hp, hpinitial, b, hbTarget, hpterm⟩ := hcompleted
      exact threadLimit_meets_frontier_of_completed hL C
        (previousNextIndex previous) B.index B.previous_lt htight a hp
        hpinitial hbTarget hpterm
    · have hyWarp : C.threadLimit Gamma a ∈ L.warpAt B.index := by
        apply threadLimit_mem_warpAt_of_cofinal_stagePrefix
          hL.limitStages C (previousNextIndex previous) B.index
          B.index_isSuccLimit B.previous_lt B.monotone
        · intro b
          let bStage : Ladder.Stage kappa :=
            ⟨b.1, by
              change b.1 < kappa.ord
              exact b.2.trans B.index.2⟩
          have hbStage : bStage < B.index := b.2
          obtain ⟨j, hj⟩ := B.cofinal bStage hbStage
          exact ⟨j, hj.le⟩
        · exact hprefix
      by_contra hmiss
      have hyInessential : C.threadLimit Gamma a ∈
          Gamma.inessentialPaths (L.warpAt B.index) := by
        apply Gamma.mem_inessentialPaths_of_misses_essentialFrontier hyWarp
        rwa [← L.frontier_eq_essential_terminalFrontier
          hDeferred.roofsSourceAtStages B.index]
      have hyLimit : C.threadLimit Gamma a ∈ L.limitWarp :=
        hDeferred.halfwayGeometry.mem_limitWarp_of_mem_inessential hyInessential
      have hclosed := hHit (C.threadLimit Gamma a) hyLimit
      apply hmiss
      apply frontier_hit_at_lub_of_closed
        (previousNextIndex previous) B.index B.monotone B.range_isLUB
        hclosed
      intro j
      refine ⟨(previous j.1 j.2).next_mem, ?_⟩
      obtain ⟨p, hp, hpinitial⟩ := by
        have haStage : a.1 ∈ Gamma.initialSet (C.stage j) := by
          rw [(htight j).1.initialSet_eq]
          have haA : a.1 ∈ A := by
            obtain ⟨l, hal⟩ := Set.mem_iUnion.1 a.2
            rw [(htight l).1.initialSet_eq] at hal
            exact hal
          exact haA
        exact haStage
      obtain ⟨f, rfl, _hfEssential, hfFrontier⟩ :=
        hprefix j p hp hpinitial
      refine ⟨f.finish, hfFrontier, ?_⟩
      exact (C.mem_support_threadLimit_iff Gamma a f.finish).2
        ⟨j, .inl f, hp, hpinitial, f.finish_mem_support⟩
  obtain ⟨hlink, hclosed, hroofLimit, hextends⟩ :=
    tightAnnularLimit_of_threads_meet_frontier hNorm hL hA C
      (previousNextIndex previous) B.index B.previous_lt htight hroof hZ
      hthreads
  refine ⟨hlink, hclosed, hroofLimit, hextends, ?_⟩
  intro p hp
  obtain ⟨a, rfl⟩ := hp
  rcases completed_or_all_stagePrefix hi previous hprevious a with
    hcompleted | hprefix
  · obtain ⟨j, q, hq, hqinitial, b, hbTarget, hqterm⟩ := hcompleted
    left
    exact ⟨b, hbTarget,
      DirectedPath.Path.terminal_chainLimit_of_cofinal
        (C.thread Gamma a.1) (C.thread_nonempty Gamma a)
        (C.thread_isChain Gamma a.1)
        (terminalCofinal_of_thread_member_target hNorm C a hq
          hqinitial hbTarget hqterm)⟩
  · right
    have hpWarp : C.threadLimit Gamma a ∈ L.warpAt B.index := by
      apply threadLimit_mem_warpAt_of_cofinal_stagePrefix
        hL.limitStages C (previousNextIndex previous) B.index
        B.index_isSuccLimit B.previous_lt B.monotone
      · intro b
        let bStage : Ladder.Stage kappa :=
          ⟨b.1, by
            change b.1 < kappa.ord
            exact b.2.trans B.index.2⟩
        have hbStage : bStage < B.index := b.2
        obtain ⟨j, hj⟩ := B.cofinal bStage hbStage
        exact ⟨j, hj.le⟩
      · exact hprefix
    obtain ⟨f, hf⟩ := hlink.1.finiteCharacter
      (show C.threadLimit Gamma a ∈ C.limitPaths Gamma from ⟨a, rfl⟩)
    have hfFrontier : f.finish ∈ L.frontier B.index := by
      apply hlink.1.terminalFrontier_subset
      exact ⟨C.threadLimit Gamma a, ⟨a, rfl⟩, by
        simpa only [hf, Gamma.terminal?_finite]⟩
    refine ⟨f, hf, ?_, hfFrontier⟩
    rw [hf] at hpWarp
    refine ⟨hpWarp, f.finish, ?_, ?_⟩
    · simp only [Gamma.terminal?_finite]
    · rw [← L.frontier_eq_essential_terminalFrontier
        hDeferred.roofsSourceAtStages B.index]
      exact hfFrontier

/-- The concrete limit compiler.  Its only source-Lemma-7.28 input is the
directed-supremum closure of the hit stages of final ladder components. -/
theorem limitStageCompiler_of_hitClosure
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized)
    (hL : SpliceLadderGeometry Gamma L)
    (hDeferred : DWeb.KappaLadder.Deferred.IsDeferredLegal L)
    (hA : A ⊆ Gamma.source)
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      Gamma L Sigma Z)
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma) :
    ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        SliceSplice.StagePayload Gamma L Sigma Z),
      Order.IsSuccLimit i.1 →
      (∀ j (hji : j < i),
        SliceSplice.IsValidStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji)) →
      ∃ D : TightStageData Gamma L Sigma Z,
        D.IsSound (A := A) (request := request) hNorm hA i previous := by
  intro i previous hi hprevious
  let C := limitHistoryChain previous hprevious
  have : Nonempty (Set.Iio i) :=
    ⟨⟨⟨0, hi.bot_lt.trans i.2⟩, hi.bot_lt⟩⟩
  let B : LimitIndexData Sigma i (previousNextIndex previous) :=
    Classical.choice
      (exists_limitIndexData_of_validHistory hL.regular hSigma i hi
        previous hprevious)
  let W₀ : Set Gamma.DPath := C.limitPaths Gamma
  have hbase :
      TightLinkageBetween Gamma A (L.frontier B.index) W₀ ∧
        Gamma.vertexSet W₀ ⊆ Z ∧
        Gamma.vertexSet W₀ ⊆ Gamma.roof (L.frontier B.index) ∧
        (∀ j, Gamma.ForwardExtension (C.stage j) W₀) ∧
        (∀ p ∈ W₀,
          (∃ b ∈ Gamma.target, Gamma.terminal? p = some b) ∨
            SliceSplice.StagePrefix Gamma L B.index p) := by
    simpa only [C, W₀] using
      exists_tight_limitFamily hNorm hL hDeferred hA hHit hi previous
        hprevious B
  let U : Set V := {x | ∃ a : A, request i = some a ∧
    ∃ p ∈ W₀, p.initial = a.1 ∧ Gamma.terminal? p = some x}
  have hUsub : U ⊆ L.frontier B.index ∩ Z := by
    rintro x ⟨a, ha, p, hp, hpinitial, hpterm⟩
    constructor
    · exact hbase.1.1.terminalFrontier_subset ⟨p, hp, hpterm⟩
    · exact hbase.2.1 ⟨p, hp, Gamma.terminal_mem_support hpterm⟩
  have hUsubsingleton : U.Subsingleton := by
    rintro x ⟨a, ha, p, hp, hpinitial, hpterm⟩
      y ⟨a', ha', q, hq, hqinitial, hqterm⟩
    have haa' : a = a' := Option.some.inj (ha.symm.trans ha')
    subst a'
    have hpq : p = q :=
      DWeb.IsWarp.eq_of_initial_eq Gamma hbase.1.1.isWarp hp hq
        (hpinitial.trans hqinitial.symm)
    subst q
    exact Option.some.inj (hpterm.symm.trans hqterm)
  have hUsmall : #U < kappa := by
    let f : U → PUnit := fun _ ↦ PUnit.unit
    have hf : Function.Injective f := by
      intro x y _
      exact Subtype.ext (hUsubsingleton x.2 y.2)
    have hUone : #U ≤ 1 := by
      simpa only [Cardinal.mk_punit] using Cardinal.mk_le_of_injective hf
    exact hUone.trans_lt
      (Cardinal.one_lt_aleph0.trans_le hL.regular.aleph0_le)
  obtain ⟨gamma, hgamma, hBgamma, T, hT⟩ :=
    hslices B.index B.index_mem U hUsub hUsmall
  let hcompat : Gamma.StarCompatible W₀ T :=
    starCompatible_of_annular (hL.frontiersEssential B.index)
      hbase.2.2.1 hbase.1.2 hT.1.1.1
  let W : Set Gamma.DPath := Gamma.star hcompat
  have hstep :
      TightLinkageBetween Gamma A (L.frontier gamma) W ∧
        Gamma.ForwardExtension W₀ W ∧
        Gamma.vertexSet W ⊆ Z ∧
        Gamma.vertexSet W ⊆ Gamma.roof (L.frontier gamma) := by
    simpa only [W, hcompat] using
      (tightAnnularSuccessor hNorm hL hA hBgamma hclosed hbase.1
        hbase.2.1 hbase.2.2.1 hT.1)
  let D : TightStageData Gamma L Sigma Z := {
    stageIndex := B.index
    stageIndex_mem := B.index_mem
    scheduled := U
    scheduled_subset := hUsub
    scheduled_small := hUsmall
    nextIndex := gamma
    next_mem := hgamma
    index_lt_next := hBgamma
    slice := T
    sliceControlled := hT
    family := W }
  refine ⟨D, ?_⟩
  change TightLinkageBetween Gamma A (L.frontier gamma) W ∧
    Gamma.vertexSet W ⊆ Z ∧
    Gamma.vertexSet W ⊆ Gamma.roof (L.frontier gamma) ∧
    (∀ j (hji : j < i),
      (previous j hji).nextIndex ≤ B.index) ∧
    (∀ p ∈ W,
      (∃ b ∈ Gamma.target, Gamma.terminal? p = some b) ∨
        IsStagePrefix Gamma L gamma p ∨
        ∃ x ∈ stageMaverickTerminals Gamma L gamma T,
          Gamma.terminal? p = some x) ∧
    (∀ j (hji : j < i),
      Gamma.ForwardExtension (previous j hji).family W) ∧
    (∀ j (hji : j < i), ∀ p ∈ (previous j hji).family,
      (∃ x ∈ (previous j hji).pendingTerminals,
        Gamma.terminal? p = some x) →
      ∃ q ∈ W, Gamma.Extends p q ∧
        ∃ b ∈ Gamma.target, Gamma.terminal? q = some b) ∧
    ∀ a : A, request i = some a →
      ∃ p ∈ W, p.initial = a.1 ∧
        ∃ b ∈ Gamma.target, Gamma.terminal? p = some b
  refine ⟨hstep.1, hstep.2.2.1, hstep.2.2.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hji
    exact B.previous_le ⟨j, hji⟩
  · rintro r ⟨p, rfl⟩
    rcases hbase.2.2.2.2 p p.2 with hpTarget | hpPrefix
    · left
      obtain ⟨b, hbTarget, hpterm⟩ := hpTarget
      have heq : p.1 = Gamma.starPath hcompat p :=
        eq_of_extends_of_terminal_mem_target hNorm
          (Gamma.extends_starPath hcompat p) hpterm hbTarget
      exact ⟨b, hbTarget, heq ▸ hpterm⟩
    · rcases starPath_stagePrefix_or_maverickTerminal hL hT hcompat p
        hpPrefix with hpNew | hpPending
      · exact Or.inr (Or.inl hpNew)
      · exact Or.inr (Or.inr hpPending)
  · intro j hji
    have hjBase : Gamma.ForwardExtension (previous j hji).family W₀ :=
      hbase.2.2.2.1 ⟨j, hji⟩
    exact Gamma.forwardExtension_trans hjBase hstep.2.1
  · intro j hji p hp hpPending
    have hsucc : Order.succ j.1 < i.1 := hi.succ_lt hji
    let lStage : Ladder.Stage kappa :=
      ⟨Order.succ j.1, hsucc.trans i.2⟩
    have hjl : j < lStage := Order.lt_succ j.1
    obtain ⟨q, hq, hpq, b, hbTarget, hqterm⟩ :=
      (hprevious lStage hsucc).resolves_previous_pending
        j hjl p hp hpPending
    obtain ⟨r, hr, hqr⟩ :=
      (hbase.2.2.2.1 ⟨lStage, hsucc⟩).1 q hq
    have hqrEq : q = r :=
      eq_of_extends_of_terminal_mem_target hNorm hqr hqterm hbTarget
    have hqW₀ : q ∈ W₀ := hqrEq.symm ▸ hr
    let qs : W₀ := ⟨q, hqW₀⟩
    have hqStar : q = Gamma.starPath hcompat qs :=
      eq_of_extends_of_terminal_mem_target hNorm
        (Gamma.extends_starPath hcompat qs) hqterm hbTarget
    refine ⟨q, ?_, hpq, b, hbTarget, hqterm⟩
    exact hqStar.symm ▸ (show Gamma.starPath hcompat qs ∈ W from ⟨qs, rfl⟩)
  · intro a ha
    have haInitial : a.1 ∈ Gamma.initialSet W₀ := by
      rw [hbase.1.1.initialSet_eq]
      exact a.2
    obtain ⟨p, hp, hpinitial⟩ := haInitial
    obtain ⟨f, hpf⟩ := hbase.1.1.finiteCharacter hp
    have hpterm : Gamma.terminal? p = some f.finish := by
      simp only [hpf, Gamma.terminal?_finite]
    have hu : f.finish ∈ U :=
      ⟨a, ha, p, hp, hpinitial, hpterm⟩
    obtain ⟨r, hr, hrinitial, b, hbTarget, hrterm⟩ :=
      star_realizes_requested_terminal hNorm hT.1.1.1.1 hcompat hp
        hpterm hu (hUsub hu).1
    exact ⟨r, hr, hrinitial.trans hpinitial,
      b, hbTarget, hrterm⟩

/-- The deferred-bookkeeping wrapper exposes every additional premise used
to produce source Lemma 7.28.  In particular, the path-local limit-miss
statement is explicit rather than inferred from deferred legality. -/
theorem limitStageCompiler_of_deferred
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized)
    (hL : SpliceLadderGeometry Gamma L)
    (hDeferred : DWeb.KappaLadder.Deferred.IsDeferredLegal L)
    (hA : A ⊆ Gamma.source)
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      Gamma L Sigma Z)
    (hmarkerOutside :
      DWeb.KappaLadder.Deferred.MarkersOutsideCurrentWarp Gamma L)
    (hmiss : DWeb.KappaLadder.Deferred.LimitMissesAreInessential
      Gamma L Sigma)
    (havoid : Disjoint Sigma (DWeb.KappaLadder.Deferred.phi L)) :
    ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        SliceSplice.StagePayload Gamma L Sigma Z),
      Order.IsSuccLimit i.1 →
      (∀ j (hji : j < i),
        SliceSplice.IsValidStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji)) →
      ∃ D : TightStageData Gamma L Sigma Z,
        D.IsSound (A := A) (request := request) hNorm hA i previous := by
  apply limitStageCompiler_of_hitClosure hNorm hL hDeferred hA hclosed
    hSigma hslices
  exact DWeb.KappaLadder.Deferred.limitHitClosure_of_club hDeferred Sigma
    hSigma hmarkerOutside hmiss havoid

/-- The actual canonical deferred-ladder limit compiler.  Marker freshness
and the missed-limit-frontier theorem are properties of the canonical
construction, so the only bookkeeping input left at this interface is that
the recursion club avoids the deferred obstruction set. -/
theorem canonicalDeferredLadder_limitStageCompiler
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    (preferred : Ladder.Stage kappa → Option V)
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized)
    (hkappa : kappa.IsRegular)
    (huncountable : Cardinal.aleph0 < kappa)
    (hA : A ⊆ Gamma.source)
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma
      (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
        Gamma kappa preferred) Z)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      Gamma
        (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
          Gamma kappa preferred)
        Sigma Z)
    (havoid : Disjoint Sigma
      (DWeb.KappaLadder.Deferred.phi
        (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
          Gamma kappa preferred))) :
    ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        SliceSplice.StagePayload Gamma
          (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
            Gamma kappa preferred)
          Sigma Z),
      Order.IsSuccLimit i.1 →
      (∀ j (hji : j < i),
        SliceSplice.IsValidStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji)) →
      ∃ D : TightStageData Gamma
          (DWeb.KappaLadder.Deferred.canonicalDeferredLadder
            Gamma kappa preferred)
          Sigma Z,
        D.IsSound (A := A) (request := request) hNorm hA i previous := by
  let L := DWeb.KappaLadder.Deferred.canonicalDeferredLadder
    Gamma kappa preferred
  have hNoEnter : Gamma.NoEdgeEnters Gamma.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hDeferred : DWeb.KappaLadder.Deferred.IsDeferredLegal L :=
    DWeb.KappaLadder.Deferred.canonicalDeferredLadder_isDeferredLegal
      preferred hkappa huncountable hNoEnter
  have hL : SpliceLadderGeometry Gamma L :=
    ⟨hDeferred.regular, hDeferred.initialStage, hDeferred.limitStages,
      hDeferred.warpStages, hDeferred.frontiersEssential,
      hDeferred.frontierChronology, hDeferred.strictFrontierChronology⟩
  apply limitStageCompiler_of_deferred hNorm hL hDeferred hA hclosed
    hSigma hslices
  · intro a y hy
    exact DWeb.KappaLadder.Deferred.canonicalDeferredLadder_marker_not_mem_currentVertexSet
      preferred hNoEnter a y hy
  · exact
      DWeb.KappaLadder.Deferred.canonicalDeferredLadder_limitMissesAreInessential
        preferred hkappa huncountable hNoEnter Sigma
  · exact havoid

end LocalConstruction
end SliceSpliceConstructor
end CardinalInduction
end Erdos599
