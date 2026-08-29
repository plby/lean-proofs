/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryFinite
import ErdosProblems.Erdos599.AlternatingDichotomy
import ErdosProblems.Erdos599.TerminalContactSwitch
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Canonical backward switch for a split-grounded finite boundary collision

The residual blocker-to-finite branch identifies the finite point as the
terminal of the retained fragment's whole limiting-ladder parent.  That
parent is a grounded record, so its initial vertex is an original source.
Traversing the whole finite parent backwards is therefore an unconditional
one-link terminal-contact switch.  This uses only sound split-legality
fields.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev FiniteSwitchInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

/-- A finite source on a retained fragment belongs to the fragment's
grounded recorded parent. -/
theorem splitGrounded_fragment_parent_grounded_of_finiteSource_mem_support
    (P : (FiniteSwitchInput (L := L) (hL := hL)).Fragment)
    {c : V}
    (hcFinite : c ∈ (FiniteSwitchInput (L := L) (hL := hL)).finiteSource)
    (hcP : c ∈ P.path.support) :
    ∃ a : Ladder.Stage kappa,
      a ∈ L.phiGround ∧ L.chosen a = some P.parent := by
  change c ∈ L.groundedFiniteTerminalSet at hcFinite
  obtain ⟨a, ha, q, hchosen, hterminal⟩ := hcFinite
  have hqLimit : q ∈ L.limitWarp :=
    (L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
      (by
        change a.1 + 1 ≤ kappa.ord
        exact (Order.add_one_le_iff).2 a.2)).1
  have hcQ : c ∈ q.support := Gamma.terminal_mem_support hterminal
  have hcParent : c ∈ P.parent.support := P.support_subset hcP
  have hparent : q = P.parent :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (hL.legal.warpStages (Ladder.finalStage kappa))
      hqLimit P.parent_mem hcQ hcParent
  exact ⟨a, ha.1, hchosen.trans (congrArg some hparent)⟩

/-- The same grounded parent ends at the finite fragment terminal. -/
theorem splitGrounded_fragment_parent_terminal_of_finiteSource_terminal
    (P : (FiniteSwitchInput (L := L) (hL := hL)).Fragment)
    {c : V}
    (hcFinite : c ∈ (FiniteSwitchInput (L := L) (hL := hL)).finiteSource)
    (hcTerminal : P.path.terminal? = some c) :
    Gamma.terminal? P.parent = some c := by
  change c ∈ L.groundedFiniteTerminalSet at hcFinite
  obtain ⟨a, ha, q, hchosen, hqTerminal⟩ := hcFinite
  have hqLimit : q ∈ L.limitWarp :=
    (L.recorded_mem_inessential hL.legal.recordedPathsPersist hchosen
      (by
        change a.1 + 1 ≤ kappa.ord
        exact (Order.add_one_le_iff).2 a.2)).1
  have hcQ : c ∈ q.support := Gamma.terminal_mem_support hqTerminal
  have hcParent : c ∈ P.parent.support :=
    P.support_subset (Gamma.terminal_mem_support hcTerminal)
  have hparent : q = P.parent :=
    Alternating.DWeb.IsWarp.eq_of_mem_support
      (hL.legal.warpStages (Ladder.finalStage kappa))
      hqLimit P.parent_mem hcQ hcParent
  simpa only [← hparent] using hqTerminal

private theorem walk_eq_nil_of_isPath
    {D : Digraph V} {x : V}
    (p : Walk D x x) (hp : p.IsPath) : p = .nil := by
  cases p with
  | nil => rfl
  | @cons _ y _ h q =>
      exact False.elim ((List.nodup_cons.mp hp).1 q.end_mem_support)

private theorem finitePath_support_eq_singleton_of_start_eq_finish
    {D : Digraph V} (p : FinitePath D)
    (h : p.start = p.finish) : p.support = {p.start} := by
  rcases p with ⟨start, finish, walk, isPath⟩
  dsimp at h ⊢
  subst finish
  have hw : walk = .nil := walk_eq_nil_of_isPath walk isPath
  subst walk
  ext x
  change x ∈ [start] ↔ x = start
  simp

/-- The exact residual finite-boundary case supplies a one-link backward
terminal-contact switch along its whole grounded parent. -/
theorem SplitGroundedBlockingFiniteTerminalCase.exists_parentBackwardTerminalContactSwitching
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (hcase : SplitGroundedBlockingFiniteTerminalCase O) :
    ∃ (Q : Alternating.FiniteTrace Gamma.graph) (u : V),
      Alternating.IsTerminalContactSwitching
        (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths Q u ∧
      Q.initial = O.later ∧
      (Alternating.AltPath.finite Q).directionEdges .forward = ∅ ∧
      u ∈ Gamma.initialSet
        (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths ∧
      u ∈ Gamma.source := by
  obtain ⟨P, _hPG0, hblockable, hblocking, hterminal,
      hlaterFinite, _hlaterCut⟩ := hcase
  have hparentTerminal : Gamma.terminal? P.parent = some O.later :=
    L.splitGrounded_fragment_parent_terminal_of_finiteSource_terminal
      (hL := hL) P hlaterFinite hterminal
  have hparentGrounded :=
    L.splitGrounded_fragment_parent_grounded_of_finiteSource_mem_support
      (hL := hL) P hlaterFinite
        (Gamma.terminal_mem_support hterminal)
  obtain ⟨a, haGround, hchosen⟩ := hparentGrounded
  obtain ⟨q, hqChosen, hqSource⟩ := haGround
  have hqParent : q = P.parent :=
    Option.some.inj (hqChosen.symm.trans hchosen)
  have hparentSource : P.parent.initial ∈ Gamma.source := by
    simpa only [← hqParent] using hqSource
  have hbSupport : GroundingCut.blockingPoint
      (FiniteSwitchInput (L := L) (hL := hL)) S.cut P ∈
        P.parent.support :=
    P.support_subset (GroundingCut.blockingPoint_mem_support
      (FiniteSwitchInput (L := L) (hL := hL)) S.cut P hblockable)
  have hbNe : GroundingCut.blockingPoint
      (FiniteSwitchInput (L := L) (hL := hL)) S.cut P ≠ O.later := by
    intro heq
    exact O.distinct (hblocking.symm.trans heq)
  cases hparent : P.parent with
  | inr r =>
      have : (none : Option V) = some O.later := by
        simpa only [hparent, DWeb.terminal?_ray] using hparentTerminal
      cases this
  | inl p =>
      have hpMember : (Sum.inl p : Gamma.DPath) ∈
          (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths := by
        simpa only [← hparent] using P.parent_mem
      have hpFinish : p.finish = O.later := by
        simpa only [hparent, DWeb.terminal?_finite,
          Option.some.injEq] using hparentTerminal
      have hbSupportP : GroundingCut.blockingPoint
          (FiniteSwitchInput (L := L) (hL := hL)) S.cut P ∈
            p.support := by
        rw [hparent] at hbSupport
        exact hbSupport
      have hpNontrivial : p.start ≠ p.finish := by
        intro hstartFinish
        have hbEq : GroundingCut.blockingPoint
            (FiniteSwitchInput (L := L) (hL := hL)) S.cut P = p.start := by
          rw [finitePath_support_eq_singleton_of_start_eq_finish
            p hstartFinish] at hbSupportP
          simpa using hbSupportP
        apply hbNe
        exact hbEq.trans (hstartFinish.trans hpFinish)
      let l : Alternating.Link Gamma.graph :=
        ⟨p, .backward, hpNontrivial⟩
      let Q : Alternating.FiniteTrace Gamma.graph :=
        Alternating.FiniteTrace.singleton l
      have hbracket : Alternating.IsBracketSwitchingAlternating
          (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths
          (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths
          (.finite Q) := by
        simpa only [Q, l, Alternating.AltPath.single] using
          (Alternating.isBracketSwitchingAlternating_single_backward
            (U := (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths)
            (Z := (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths)
            (FiniteSwitchInput (L := L) (hL := hL)).ladder.disjoint
            p hpMember hpNontrivial)
      have hswitch := hbracket.isSwitchingAlternating
      have huInitial : p.start ∈ Gamma.initialSet
          (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths :=
        ⟨Sum.inl p, hpMember, rfl⟩
      have huOutgoing : Alternating.HasOutgoing
          (Alternating.familyEdges
            (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths)
          p.start := by
        obtain ⟨z, hz⟩ :=
          Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            p p.start_mem_support hpNontrivial
        exact ⟨z, Set.mem_iUnion.2
          ⟨Sum.inl p, Set.mem_iUnion.2 ⟨hpMember, hz⟩⟩⟩
      have hcontact : Alternating.IsTerminalContactSwitching
          (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths Q p.start := by
        refine
          { warp := hswitch.1.1
            backwardLinksOn := hswitch.1.2.1
            forwardLinksOff := hswitch.2.1
            contactsCoveredAtTerminal := ?_
            firstForwardInitialOff := hswitch.1.2.2.1
            terminal_eq := by simp [Q, l, Alternating.Link.exit]
            terminal_mem_initialSet := huInitial
            terminal_outgoing_or_isolated := Or.inl huOutgoing
            noForwardOutgoingAtTerminal := by
              rintro ⟨z, hz⟩
              simp only [Alternating.AltPath.directionEdges,
                Set.mem_iUnion] at hz
              obtain ⟨k, hk, hdir, _he⟩ := hz
              have hkEq : k = l := by
                simp only [Alternating.AltPath.links,
                  Alternating.FiniteTrace.links, Set.mem_range] at hk
                obtain ⟨i, rfl⟩ := hk
                have hi : i = 0 := Fin.eq_zero i
                subst i
                rfl
              subst k
              simp [l] at hdir }
        intro x hxForward hxLadder
        exact Or.inl (hswitch.2.2 ⟨hxForward, hxLadder⟩)
      refine ⟨Q, p.start, hcontact, ?_, ?_, huInitial, ?_⟩
      · simp [Q, l, Alternating.Link.entry, hpFinish]
      · ext e
        constructor
        · intro he
          simp only [Alternating.AltPath.directionEdges,
            Set.mem_iUnion] at he
          obtain ⟨k, hk, hdir, _he⟩ := he
          have hkEq : k = l := by
            simp only [Alternating.AltPath.links,
              Alternating.FiniteTrace.links, Set.mem_range] at hk
            obtain ⟨i, rfl⟩ := hk
            have hi : i = 0 := Fin.eq_zero i
            subst i
            rfl
          subst k
          simp [l] at hdir
        · simp
      · rw [hparent] at hparentSource
        change p.start ∈ Gamma.source at hparentSource
        exact hparentSource

/-- Realize the canonical whole-parent switch as an actual warp.  Its
initial set loses the grounded parent's original-source initial and its
finite terminal frontier loses exactly the displayed later boundary point. -/
theorem SplitGroundedBlockingFiniteTerminalCase.exists_parentBackwardTerminalContactWarp
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (hcase : SplitGroundedBlockingFiniteTerminalCase O) :
    ∃ (u : V) (W : Set Gamma.DPath),
      u ∈ Gamma.initialSet
          (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths ∧
      u ∈ Gamma.source ∧
      Gamma.IsWarp W ∧
      Gamma.initialSet W =
        Gamma.initialSet
          (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths \ {u} ∧
      Gamma.terminalFrontier W =
        Gamma.terminalFrontier
          (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths \
            {O.later} := by
  obtain ⟨Q, u, hswitch, hQinitial, _hforwardEmpty,
      huInitial, huSource⟩ :=
    hcase.exists_parentBackwardTerminalContactSwitching
  have hcase' := hcase
  obtain ⟨P, _hPG0, _hblockable, _hblocking, hterminal,
      hlaterFinite, _hlaterCut⟩ := hcase'
  have hlaterFrontier : O.later ∈ Gamma.terminalFrontier
      (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths := by
    refine ⟨P.parent, P.parent_mem, ?_⟩
    exact L.splitGrounded_fragment_parent_terminal_of_finiteSource_terminal
      (hL := hL) P hlaterFinite hterminal
  obtain ⟨W, hwarp, hinitial, hterminalW⟩ :=
    Alternating.TerminalContactSwitch.exists_terminalContactSwitch_anyWarp
      (FiniteSwitchInput (L := L) (hL := hL)).ladder.paths
      Q u O.later hswitch hlaterFrontier hQinitial
  exact ⟨u, W, huInitial, huSource, hwarp, hinitial, hterminalW⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedBlockingFiniteTerminalCase.exists_parentBackwardTerminalContactSwitching
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedBlockingFiniteTerminalCase.exists_parentBackwardTerminalContactWarp
