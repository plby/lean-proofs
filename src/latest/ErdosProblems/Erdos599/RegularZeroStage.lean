/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceSpliceConstructor

/-!
# The zero-stage compiler for the regular slice recursion

A club of ladder stages need not contain ordinal zero.  Consequently the
first recursive payload cannot in general record its controlled slice as a
zero-based club slice.  The source-faithful construction uses two steps:

1. one explicit tracked slice from the genuine zero frontier to a first
   club point builds the initial partial source linkage;
2. the ordinary controlled-slice table starts at that club point, schedules
   the optional stage-zero request, and advances to a later club point.

The only additional geometric premise below is existence of the first
zero-to-club tracked slice.  It is strictly local, contains no recursive
operation or completed linkage, and does not assert that zero belongs to
the club.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceSpliceConstructor
namespace LocalConstruction

open SliceSpliceSource

universe u

variable {V : Type u}

/-- The one base slice which is not supplied by the club-indexed controlled
slice table: it starts at the genuine zero frontier and ends at a member of
the club. -/
def HasFirstTrackedSlice {kappa : Cardinal.{u}}
    (Gamma : DWeb V) (L : Gamma.KappaLadder kappa)
    (Sigma : Set (Ladder.Stage kappa)) (Z : Set V)
    (hkappa : kappa.IsRegular) : Prop :=
  ∃ alpha ∈ Sigma, ∃ T : Set Gamma.DPath,
    SliceCandidate.IsTrackedTightAnnularControlledSlice
      Gamma L Z ⟨0, hkappa.ord_pos⟩ alpha ∅ T

private theorem appendFinite_trivial
    {Gamma : DWeb V} (x : V) (q : Gamma.DPath)
    (hstart : q.initial = x)
    (hinter : (DirectedPath.FinitePath.trivial Gamma.graph x).support ∩
      q.support ⊆ {x}) :
    DirectedPath.Path.appendFinite
      (DirectedPath.FinitePath.trivial Gamma.graph x) q
      (by simpa using hstart) (by simpa using hinter) = q := by
  rcases q with q | r
  · cases q with
    | mk start finish walk isPath =>
      dsimp only [DirectedPath.Path.initial] at hstart
      subst start
      rfl
  · dsimp only [DirectedPath.Path.initial] at hstart
    subst x
    rfl

/-- Every member of the genuine zero-to-club slice is either the exact
canonical prefix at its right endpoint or a stage-relative maverick. -/
theorem initialRestriction_path_stagePrefix_or_maverickTerminal
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa} {Z U : Set V}
    {beta : Ladder.Stage kappa} {T : Set Gamma.DPath}
    (hL : SpliceLadderGeometry Gamma L)
    (hT : SliceCandidate.IsTrackedTightAnnularControlledSlice
      Gamma L Z ⟨0, hL.regular.ord_pos⟩ beta U T)
    (p : initialRestriction Gamma T (Gamma.source ∩ Z)) :
    IsStagePrefix Gamma L beta p.1 ∨
      ∃ x ∈ stageMaverickTerminals Gamma L beta T,
        Gamma.terminal? p.1 = some x := by
  have hpT : p.1 ∈ T := p.2.1
  by_cases hpOrdinary :
      ControlledSlices.IsLadderFragment Gamma (L.warpAt beta) p.1
  · obtain ⟨left, right, segment, hpsegment, hleftEssential,
        hrightEssential, _hleftFrontier, hrightFrontier,
        hsegmentStart, hsegmentInter, _hinterEq, happend⟩ :=
      hT.2.1 p.1 hpT hpOrdinary
    have hleftWarp : (Sum.inl left : Gamma.DPath) ∈
        L.warpAt ⟨0, hL.regular.ord_pos⟩ := hleftEssential.1
    change (Sum.inl left : Gamma.DPath) ∈
      L.accumulated (Ladder.zeroStage kappa) at hleftWarp
    rw [hL.initialStage] at hleftWarp
    obtain ⟨x, _hxSource, hxleft⟩ := hleftWarp
    have hleft : left = DirectedPath.FinitePath.trivial Gamma.graph x := by
      exact Sum.inl.inj hxleft.symm
    subst left
    left
    refine ⟨right, ?_, hrightEssential, hrightFrontier⟩
    rw [hpsegment]
    have happend' := happend
    rw [appendFinite_trivial x (.inl segment) (by simpa using hsegmentStart)
      (by simpa using hsegmentInter)] at happend'
    exact happend'
  · right
    have hpMaverick : p.1 ∈
        ControlledSlices.sliceMavericks Gamma (L.warpAt beta) T :=
      ⟨hpT, hpOrdinary⟩
    obtain ⟨f, hpf⟩ := hT.1.1.1.1.1.finiteCharacter hpT
    refine ⟨f.finish, ⟨p.1, hpMaverick, ?_⟩, ?_⟩
    · rw [hpf]
      rfl
    · rw [hpf]
      rfl

/-- The positive zero-case compiler consumed by
`hasTightStageData_of_stageCaseCompilers`.  The explicit first slice builds
the initial source--frontier linkage; the club-indexed slice schedules the
optional request at recursion index zero. -/
theorem zeroStageCompiler_of_firstTrackedSlice
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized) (hUnhindered : Gamma.IsUnhindered)
    (hL : SpliceLadderGeometry Gamma L) (hA : A = Gamma.source ∩ Z)
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      Gamma L Sigma Z)
    (hfirst : HasFirstTrackedSlice Gamma L Sigma Z hL.regular) :
    ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        SliceSplice.StagePayload Gamma L Sigma Z),
      i.1 = 0 →
      (∀ j (hji : j < i),
        SliceSplice.IsValidStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji)) →
      ∃ D : TightStageData Gamma L Sigma Z,
        D.IsSound (A := A) (request := request) hNorm
          (hA.symm ▸ Set.inter_subset_left) i previous := by
  intro i previous hi _hprevious
  obtain ⟨alpha, halpha, T₀, hT₀⟩ := hfirst
  let P : Set Gamma.DPath :=
    initialRestriction Gamma T₀ (Gamma.source ∩ Z)
  have hfirstFrontier :
      L.frontier ⟨0, hL.regular.ord_pos⟩ = Gamma.source :=
    frontier_zero_eq_source_of_initialStage hNorm hUnhindered
      hL.regular hL.initialStage
  have hsourceT₀ := sourceTightAnnularSlice_of_candidate hT₀.1.1
  have hlinkT₀ : TightLinkageBetween Gamma Gamma.source
      (L.frontier alpha) T₀ := by
    simpa only [hfirstFrontier] using
      (tightLinkageBetween_of_tightAnnularSlice hsourceT₀)
  have hPtight : TightLinkageBetween Gamma (Gamma.source ∩ Z)
      (L.frontier alpha) P :=
    hlinkT₀.initialRestriction Set.inter_subset_left
  have hPclosed : Gamma.vertexSet P ⊆ Z := by
    apply vertexSet_initialRestriction_subset_of_controlledSlice
      hclosed Set.inter_subset_right
    exact SliceSplice.controlledSlice_of_annularControlledSlice
      ⟨hT₀.1.1.1, hT₀.1.2⟩
  have hProof : Gamma.vertexSet P ⊆
      Gamma.roof (L.frontier alpha) :=
    (vertexSet_initialRestriction_subset Gamma T₀
      (Gamma.source ∩ Z)).trans (fun _ hx ↦ (hT₀.1.1.1.2 hx).2)
  have hPtightA : TightLinkageBetween Gamma A (L.frontier alpha) P := by
    simpa only [hA] using hPtight
  by_cases hrequested : ∃ a : A, request i = some a
  · obtain ⟨a₀, ha₀⟩ := hrequested
    obtain ⟨p₀, hp₀, hp₀initial, u, huFrontier, hp₀terminal⟩ :=
      exists_member_terminal_of_linkage hPtightA.1 a₀.2
    let U : Set V := stageMaverickTerminals Gamma L alpha T₀ ∪ {u}
    have hUsub : U ⊆ L.frontier alpha ∩ Z := by
      intro x hx
      rcases hx with hxPending | hxRequested
      · exact ⟨stageMaverickTerminals_subset_frontier hT₀ hxPending,
          stageMaverickTerminals_subset_closure hT₀ hxPending⟩
      · have hxu : x = u := Set.mem_singleton_iff.1 hxRequested
        subst x
        exact ⟨huFrontier,
          hPclosed ⟨p₀, hp₀, Gamma.terminal_mem_support hp₀terminal⟩⟩
    have hUsmall : #U < kappa := by
      apply RegularCardinal.mk_union_lt hL.regular
      · exact stageMaverickTerminals_small hT₀
      · rw [Cardinal.mk_singleton]
        exact Cardinal.one_lt_aleph0.trans_le hL.regular.aleph0_le
    obtain ⟨beta, hbeta, hab, T, hT⟩ :=
      hslices alpha halpha U hUsub hUsmall
    let hcompat : Gamma.StarCompatible P T :=
      starCompatible_of_annular (hL.frontiersEssential alpha)
        hProof hPtightA.2 hT.1.1.1
    let W : Set Gamma.DPath := Gamma.star hcompat
    have hstep :
        TightLinkageBetween Gamma A (L.frontier beta) W ∧
          Gamma.ForwardExtension P W ∧
          Gamma.vertexSet W ⊆ Z ∧
          Gamma.vertexSet W ⊆ Gamma.roof (L.frontier beta) := by
      simpa only [hcompat, W] using
        (tightAnnularSuccessor hNorm hL
          (hA.symm ▸ Set.inter_subset_left) hab hclosed hPtightA
          hPclosed hProof hT.1)
    let D : TightStageData Gamma L Sigma Z := {
      stageIndex := alpha
      stageIndex_mem := halpha
      scheduled := U
      scheduled_subset := hUsub
      scheduled_small := hUsmall
      nextIndex := beta
      next_mem := hbeta
      index_lt_next := hab
      slice := T
      sliceControlled := hT
      family := W }
    refine ⟨D, ?_⟩
    change TightLinkageBetween Gamma A (L.frontier beta) W ∧
      Gamma.vertexSet W ⊆ Z ∧
      Gamma.vertexSet W ⊆ Gamma.roof (L.frontier beta) ∧
      (∀ j (hji : j < i), (previous j hji).nextIndex ≤ alpha) ∧
      (∀ r ∈ W,
        (∃ b ∈ Gamma.target, Gamma.terminal? r = some b) ∨
          IsStagePrefix Gamma L beta r ∨
          ∃ x ∈ stageMaverickTerminals Gamma L beta T,
            Gamma.terminal? r = some x) ∧
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
      have hjiValue : j.1 < i.1 := hji
      have : j.1 < 0 := hi ▸ hjiValue
      exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1) this).elim
    · intro r hr
      obtain ⟨p, rfl⟩ := hr
      let p₀' : initialRestriction Gamma T₀ (Gamma.source ∩ Z) :=
        ⟨p.1, by simpa only [P] using p.2⟩
      rcases initialRestriction_path_stagePrefix_or_maverickTerminal
          hL hT₀ p₀' with hprefix | hpending
      · rcases starPath_stagePrefix_or_maverickTerminal hL hT hcompat p
          hprefix with hnewPrefix | hnewPending
        · exact Or.inr (Or.inl hnewPrefix)
        · exact Or.inr (Or.inr hnewPending)
      · obtain ⟨x, hxPending, hpterm⟩ := hpending
        obtain ⟨r, hr, hrinitial, b, hbTarget, hrterm⟩ :=
          star_realizes_requested_terminal hNorm hT.1.1.1.1 hcompat p.2
            hpterm (show x ∈ U from Or.inl hxPending)
            (hPtightA.1.terminalFrontier_subset ⟨p.1, p.2, hpterm⟩)
        have heq : Gamma.starPath hcompat p = r :=
          DWeb.IsWarp.eq_of_initial_eq Gamma hstep.1.1.isWarp
            ⟨p, rfl⟩ hr
            ((Gamma.initial_starPath hcompat p).trans hrinitial.symm)
        exact Or.inl ⟨b, hbTarget, heq ▸ hrterm⟩
    · intro j hji
      have hjiValue : j.1 < i.1 := hji
      have : j.1 < 0 := hi ▸ hjiValue
      exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1) this).elim
    · intro j hji
      have hjiValue : j.1 < i.1 := hji
      have : j.1 < 0 := hi ▸ hjiValue
      exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1) this).elim
    · intro a ha
      have haa₀ : a = a₀ := Option.some.inj (ha.symm.trans ha₀)
      subst a
      obtain ⟨r, hr, hrinitial, b, hb, hrterminal⟩ :=
        star_realizes_requested_terminal hNorm hT.1.1.1.1 hcompat hp₀
          hp₀terminal (show u ∈ U from Or.inr (Set.mem_singleton u))
          huFrontier
      exact ⟨r, hr, hrinitial.trans hp₀initial, b, hb, hrterminal⟩
  · let U : Set V := stageMaverickTerminals Gamma L alpha T₀
    have hUsub : U ⊆ L.frontier alpha ∩ Z := by
      intro x hx
      exact ⟨stageMaverickTerminals_subset_frontier hT₀ hx,
        stageMaverickTerminals_subset_closure hT₀ hx⟩
    have hUsmall : #U < kappa := stageMaverickTerminals_small hT₀
    obtain ⟨beta, hbeta, hab, T, hT⟩ :=
      hslices alpha halpha U hUsub hUsmall
    let hcompat : Gamma.StarCompatible P T :=
      starCompatible_of_annular (hL.frontiersEssential alpha)
        hProof hPtightA.2 hT.1.1.1
    let W : Set Gamma.DPath := Gamma.star hcompat
    have hstep :
        TightLinkageBetween Gamma A (L.frontier beta) W ∧
          Gamma.ForwardExtension P W ∧
          Gamma.vertexSet W ⊆ Z ∧
          Gamma.vertexSet W ⊆ Gamma.roof (L.frontier beta) := by
      simpa only [hcompat, W] using
        (tightAnnularSuccessor hNorm hL
          (hA.symm ▸ Set.inter_subset_left) hab hclosed hPtightA
          hPclosed hProof hT.1)
    let D : TightStageData Gamma L Sigma Z := {
      stageIndex := alpha
      stageIndex_mem := halpha
      scheduled := U
      scheduled_subset := hUsub
      scheduled_small := hUsmall
      nextIndex := beta
      next_mem := hbeta
      index_lt_next := hab
      slice := T
      sliceControlled := hT
      family := W }
    refine ⟨D, ?_⟩
    change TightLinkageBetween Gamma A (L.frontier beta) W ∧
      Gamma.vertexSet W ⊆ Z ∧
      Gamma.vertexSet W ⊆ Gamma.roof (L.frontier beta) ∧
      (∀ j (hji : j < i), (previous j hji).nextIndex ≤ alpha) ∧
      (∀ r ∈ W,
        (∃ b ∈ Gamma.target, Gamma.terminal? r = some b) ∨
          IsStagePrefix Gamma L beta r ∨
          ∃ x ∈ stageMaverickTerminals Gamma L beta T,
            Gamma.terminal? r = some x) ∧
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
      have hjiValue : j.1 < i.1 := hji
      have : j.1 < 0 := hi ▸ hjiValue
      exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1) this).elim
    · intro r hr
      obtain ⟨p, rfl⟩ := hr
      let p₀' : initialRestriction Gamma T₀ (Gamma.source ∩ Z) :=
        ⟨p.1, by simpa only [P] using p.2⟩
      rcases initialRestriction_path_stagePrefix_or_maverickTerminal
          hL hT₀ p₀' with hprefix | hpending
      · rcases starPath_stagePrefix_or_maverickTerminal hL hT hcompat p
          hprefix with hnewPrefix | hnewPending
        · exact Or.inr (Or.inl hnewPrefix)
        · exact Or.inr (Or.inr hnewPending)
      · obtain ⟨x, hxPending, hpterm⟩ := hpending
        obtain ⟨r, hr, hrinitial, b, hbTarget, hrterm⟩ :=
          star_realizes_requested_terminal hNorm hT.1.1.1.1 hcompat p.2
            hpterm hxPending
            (hPtightA.1.terminalFrontier_subset ⟨p.1, p.2, hpterm⟩)
        have heq : Gamma.starPath hcompat p = r :=
          DWeb.IsWarp.eq_of_initial_eq Gamma hstep.1.1.isWarp
            ⟨p, rfl⟩ hr
            ((Gamma.initial_starPath hcompat p).trans hrinitial.symm)
        exact Or.inl ⟨b, hbTarget, heq ▸ hrterm⟩
    · intro j hji
      have hjiValue : j.1 < i.1 := hji
      have : j.1 < 0 := hi ▸ hjiValue
      exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1) this).elim
    · intro j hji
      have hjiValue : j.1 < i.1 := hji
      have : j.1 < 0 := hi ▸ hjiValue
      exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1) this).elim
    · intro a ha
      exact (hrequested ⟨a, ha⟩).elim

/-- Assemble the full local tight-stage predicate once the geometric
successor and limit compilers are supplied.  The zero compiler is discharged
by `zeroStageCompiler_of_firstTrackedSlice`, so the two displayed compiler
hypotheses are exactly the remaining local recursion obligations. -/
theorem hasTightStageData_of_firstTrackedSlice_and_stageCompilers
    {kappa : Cardinal.{u}} {Gamma : DWeb V}
    {L : Gamma.KappaLadder kappa}
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    {request : Ladder.Stage kappa → Option A}
    (hNorm : Gamma.IsNormalized) (hUnhindered : Gamma.IsUnhindered)
    (hL : SpliceLadderGeometry Gamma L) (hA : A = Gamma.source ∩ Z)
    (hclosed : SliceSplice.IsLimitWarpClosed Gamma L Z)
    (hSigma : Stationary.IsClubBelow kappa Sigma)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      Gamma L Sigma Z)
    (hfirst : HasFirstTrackedSlice Gamma L Sigma Z hL.regular)
    (hsucc : ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        SliceSplice.StagePayload Gamma L Sigma Z)
      (j : Ladder.Stage kappa) (hji : j < i),
      Order.succ j.1 = i.1 →
      (∀ l (hli : l < i),
        SliceSplice.IsValidStage request l
          (fun m hml ↦ previous m (lt_trans hml hli))
          (previous l hli)) →
      ∃ D : TightStageData Gamma L Sigma Z,
        D.IsSound (A := A) (request := request) hNorm
          (hA.symm ▸ Set.inter_subset_left) i previous)
    (hlimit : ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        SliceSplice.StagePayload Gamma L Sigma Z),
      Order.IsSuccLimit i.1 →
      (∀ j (hji : j < i),
        SliceSplice.IsValidStage request j
          (fun l hlj ↦ previous l (lt_trans hlj hji))
          (previous j hji)) →
      ∃ D : TightStageData Gamma L Sigma Z,
        D.IsSound (A := A) (request := request) hNorm
          (hA.symm ▸ Set.inter_subset_left) i previous) :
    HasTightStageData Gamma L Sigma Z A request hNorm
      (hA.symm ▸ Set.inter_subset_left) := by
  apply hasTightStageData_of_stageCaseCompilers hNorm
    (hA.symm ▸ Set.inter_subset_left) hL.regular hSigma hslices
  · exact zeroStageCompiler_of_firstTrackedSlice hNorm hUnhindered hL
      hA hclosed hslices hfirst
  · exact hsucc
  · exact hlimit

end LocalConstruction
end SliceSpliceConstructor
end CardinalInduction
end Erdos599
