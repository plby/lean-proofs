/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedTerminalFailureCompiler
import ErdosProblems.Erdos599.AlternatingDichotomy
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Canonical backward switch at a finite-source collision

The signed decoder normalization failures need not be repaired by mutating
the chronologically erased trace.  In the blocking--finite terminal branch,
the later boundary point is already the terminal of a nontrivial member of
the limiting ladder.  Traversing that entire member backwards is a one-link
terminal-contact switch.  It starts at the displayed finite-source point and
ends at the initial vertex of its ladder component, and has literally no
forward link or uncovered forward contact.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedBoundaryObstruction

private theorem walk_eq_nil_of_isPath
    {D : Digraph V} {x : V}
    (p : _root_.Erdos599.DirectedPath.Walk D x x)
    (hp : p.IsPath) : p = .nil := by
  cases p with
  | nil => rfl
  | @cons _ y _ h q =>
      exact False.elim ((List.nodup_cons.mp hp).1 q.end_mem_support)

private theorem finitePath_support_eq_singleton_of_start_eq_finish
    {D : Digraph V} (p : _root_.Erdos599.DirectedPath.FinitePath D)
    (h : p.start = p.finish) : p.support = {p.start} := by
  rcases p with ⟨start, finish, walk, isPath⟩
  dsimp at h ⊢
  subst finish
  have hw : walk = .nil := walk_eq_nil_of_isPath walk isPath
  subst walk
  ext x
  change x ∈ [start] ↔ x = start
  simp

/-- A blocking--finite terminal collision has a canonical one-link backward
terminal-contact switch along the whole grounded parent.  This construction
uniformly replaces both possible internal failures of the erased decoder. -/
theorem BlockingFiniteTerminalCase.exists_parentBackwardTerminalContactSwitching
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    (hcase : BlockingFiniteTerminalCase o) :
    ∃ (Q : FiniteTrace Gamma.graph) (u : V),
      IsTerminalContactSwitching
        (L.popularAuxiliaryInput hL.legal).ladder.paths Q u ∧
      Q.initial = o.later ∧
      u ∈ Gamma.initialSet
        (L.popularAuxiliaryInput hL.legal).ladder.paths ∧
      u ∈ Gamma.source := by
  obtain ⟨P, _hPG0, _hblockable, hblocking, hterminal, hlater⟩ :=
    hcase
  have hparentTerminal : Gamma.terminal? P.parent = some o.later :=
    L.fragment_parent_terminal_of_finiteSource_terminal
      hL.legal P hlater.1 hterminal
  have hparentGrounded :
      P.parent ∈ (L.popularAuxiliaryInput hL.legal).groundedRecords :=
    L.fragment_parent_mem_groundedRecords_of_finiteSource_mem_support
      hL.legal P hlater.1 (Gamma.terminal_mem_support hterminal)
  have hparentSource : P.parent.initial ∈ Gamma.source := by
    change ∃ a : Ladder.Stage kappa,
        a ∈ L.phiGround ∧ L.chosen a = some P.parent at hparentGrounded
    obtain ⟨a, haGround, hchosen⟩ := hparentGrounded
    change ∃ q, L.chosen a = some q ∧ q.initial ∈ Gamma.source at haGround
    obtain ⟨q, hqChosen, hqSource⟩ := haGround
    have hq : q = P.parent :=
      Option.some.inj (hqChosen.symm.trans hchosen)
    simpa only [hq] using hqSource
  have hbSupport : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P ∈ P.parent.support :=
    P.support_subset
      (GroundingCut.blockingPoint_mem_support
        (L.popularAuxiliaryInput hL.legal) S.cut P)
  have hbNe : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P ≠ o.later := by
    intro heq
    exact o.distinct (hblocking.symm.trans heq)
  cases hparent : P.parent with
  | inr r =>
      have : (none : Option V) = some o.later := by
        simpa only [hparent, DWeb.terminal?_ray] using hparentTerminal
      cases this
  | inl p =>
      have hpMember : (Sum.inl p : Gamma.DPath) ∈
          (L.popularAuxiliaryInput hL.legal).ladder.paths := by
        simpa only [← hparent] using P.parent_mem
      have hpFinish : p.finish = o.later := by
        simpa only [hparent, DWeb.terminal?_finite,
          Option.some.injEq] using hparentTerminal
      have hbSupportP : GroundingCut.blockingPoint
          (L.popularAuxiliaryInput hL.legal) S.cut P ∈ p.support := by
        rw [hparent] at hbSupport
        exact hbSupport
      have hpNontrivial : p.start ≠ p.finish := by
        intro hstartFinish
        have hbEq : GroundingCut.blockingPoint
            (L.popularAuxiliaryInput hL.legal) S.cut P = p.start := by
          rw [finitePath_support_eq_singleton_of_start_eq_finish
            p hstartFinish] at hbSupportP
          simpa using hbSupportP
        apply hbNe
        exact hbEq.trans (hstartFinish.trans hpFinish)
      let l : Link Gamma.graph := ⟨p, .backward, hpNontrivial⟩
      let Q : FiniteTrace Gamma.graph := FiniteTrace.singleton l
      have hbracket : IsBracketSwitchingAlternating
          (L.popularAuxiliaryInput hL.legal).ladder.paths
          (L.popularAuxiliaryInput hL.legal).ladder.paths
          (.finite Q) := by
        simpa only [Q, l, AltPath.single] using
          (isBracketSwitchingAlternating_single_backward
            (U := (L.popularAuxiliaryInput hL.legal).ladder.paths)
            (Z := (L.popularAuxiliaryInput hL.legal).ladder.paths)
            (L.popularAuxiliaryInput hL.legal).ladder.disjoint
            p hpMember hpNontrivial)
      have hswitch := hbracket.isSwitchingAlternating
      have huInitial : p.start ∈ Gamma.initialSet
          (L.popularAuxiliaryInput hL.legal).ladder.paths :=
        ⟨Sum.inl p, hpMember, rfl⟩
      have huOutgoing : HasOutgoing
          (familyEdges
            (L.popularAuxiliaryInput hL.legal).ladder.paths) p.start := by
        obtain ⟨z, hz⟩ :=
          _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
            p p.start_mem_support hpNontrivial
        exact ⟨z, Set.mem_iUnion.2
          ⟨Sum.inl p, Set.mem_iUnion.2 ⟨hpMember, hz⟩⟩⟩
      have hcontact : IsTerminalContactSwitching
          (L.popularAuxiliaryInput hL.legal).ladder.paths Q p.start := by
        refine
          { warp := hswitch.1.1
            backwardLinksOn := hswitch.1.2.1
            forwardLinksOff := hswitch.2.1
            contactsCoveredAtTerminal := ?_
            firstForwardInitialOff := hswitch.1.2.2.1
            terminal_eq := by simp [Q, l, Link.exit]
            terminal_mem_initialSet := huInitial
            terminal_outgoing_or_isolated := Or.inl huOutgoing
            noForwardOutgoingAtTerminal := by
              rintro ⟨z, hz⟩
              simp only [AltPath.directionEdges, Set.mem_iUnion] at hz
              obtain ⟨k, hk, hdir, _he⟩ := hz
              have hkEq : k = l := by
                simp only [AltPath.links, FiniteTrace.links,
                  Set.mem_range] at hk
                obtain ⟨i, rfl⟩ := hk
                have hi : i = 0 := Fin.eq_zero i
                subst i
                rfl
              subst k
              simp [l] at hdir }
        intro x hxForward hxLadder
        exact Or.inl (hswitch.2.2 ⟨hxForward, hxLadder⟩)
      refine ⟨Q, p.start, hcontact, ?_, huInitial, ?_⟩
      · simp [Q, l, Link.entry, hpFinish]
      · rw [hparent] at hparentSource
        change p.start ∈ Gamma.source at hparentSource
        exact hparentSource

/-- The decoder payload's internal terminal outcome is therefore irrelevant:
its collision field always supplies a normalized backward switch. -/
theorem CanonicalPrivateFiniteTerminalOutcome.exists_normalizedTerminalContactSwitching
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    {D : FirstBoundaryReduction o}
    (data : CanonicalPrivateFiniteTerminalOutcome D) :
    ∃ (Q : FiniteTrace Gamma.graph) (u : V),
      IsTerminalContactSwitching
        (L.popularAuxiliaryInput hL.legal).ladder.paths Q u ∧
      Q.initial = D.reduced.later ∧
      u ∈ Gamma.initialSet
        (L.popularAuxiliaryInput hL.legal).ladder.paths ∧
      u ∈ Gamma.source :=
  data.collision.exists_parentBackwardTerminalContactSwitching

/-- Realizing the canonical backward normalization removes exactly its
grounded-parent initial from the limiting ladder's initial set and the
displayed finite-source collision point from its terminal frontier. -/
theorem CanonicalPrivateFiniteTerminalOutcome.exists_normalizedTerminalContactWarp
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    {D : FirstBoundaryReduction o}
    (data : CanonicalPrivateFiniteTerminalOutcome D) :
    ∃ (u : V) (W : Set Gamma.DPath),
      u ∈ Gamma.initialSet
          (L.popularAuxiliaryInput hL.legal).ladder.paths ∧
      u ∈ Gamma.source ∧
      Gamma.IsWarp W ∧
      Gamma.initialSet W =
        Gamma.initialSet
          (L.popularAuxiliaryInput hL.legal).ladder.paths \ {u} ∧
      Gamma.terminalFrontier W =
        Gamma.terminalFrontier
          (L.popularAuxiliaryInput hL.legal).ladder.paths \
            {D.reduced.later} := by
  obtain ⟨Q, u, hswitch, hQinitial, huInitial, huSource⟩ :=
    data.exists_normalizedTerminalContactSwitching
  obtain ⟨_q, _Q₀, _y, _hqStart, _hqTarget, _hqAvoid,
      _hqPrivate, _hqPure, _hQInitial, _hQTerminal, _hyTarget,
      hlaterFrontier, _hyInitial, _hnoForward, _hparent, _hback⟩ :=
    data.exchange
  obtain ⟨W, hwarp, hinitial, hterminal⟩ :=
    TerminalContactSwitch.exists_terminalContactSwitch_anyWarp
      (L.popularAuxiliaryInput hL.legal).ladder.paths
      Q u D.reduced.later hswitch hlaterFrontier hQinitial
  exact ⟨u, W, huInitial, huSource, hwarp, hinitial, hterminal⟩

/-- Adapter for the pre-stopped failure compiler: all three decoder outcomes
are discharged by the same canonical backward normalization.  A downstream
argument only has to consume one honest terminal-contact switch with the
displayed collision point as its initial vertex. -/
theorem CanonicalPrivateFiniteTerminalOutcome.exists_hindrance_of_normalizedTerminalContactRepair
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    {D : FirstBoundaryReduction o}
    (data : CanonicalPrivateFiniteTerminalOutcome D)
    (repair : ∀ (Q : FiniteTrace Gamma.graph) (u : V),
      IsTerminalContactSwitching
          (L.popularAuxiliaryInput hL.legal).ladder.paths Q u →
      Q.initial = D.reduced.later →
      u ∈ Gamma.initialSet
          (L.popularAuxiliaryInput hL.legal).ladder.paths →
      u ∈ Gamma.source →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  obtain ⟨Q, u, hswitch, hQinitial, huInitial, huSource⟩ :=
    data.exists_normalizedTerminalContactSwitching
  exact repair Q u hswitch hQinitial huInitial huSource

end Assertion822PreStoppedBoundaryObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.BlockingFiniteTerminalCase.exists_parentBackwardTerminalContactSwitching
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome.exists_normalizedTerminalContactSwitching
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome.exists_normalizedTerminalContactWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome.exists_hindrance_of_normalizedTerminalContactRepair
