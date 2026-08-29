/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteSourceDuplicateExchange
import ErdosProblems.Erdos599.TerminalContactSwitch

/-!
# The terminal-contact shell for a finite-source exchange

The private finite-source compiler already supplies all endpoint data needed
by the terminal-contact switch: its endpoint is a target marker, hence an
initial point of the limiting ladder; that component is either isolated or
has an old outgoing edge; and chronological erasure ensures that no inserted
forward edge leaves the endpoint.

This file packages those unconditional endpoint facts.  The only remaining
input is the internal switching geometry of the decoded trace, expressed by
`IsTerminalRelaxedAlternating` itself.  Thus downstream work cannot
accidentally re-introduce an unnecessary non-isolation assumption at a fresh
marker.
-/

noncomputable section

namespace Erdos599

namespace Alternating

open Set

universe u

variable {V : Type u} {D : Digraph V}

/-- The initial point of a finite trace whose first link is forward cannot
occur on a backward link of the same trace.  This is a direct consequence
of the ordered compatibility clauses, including the adjacent-link case. -/
theorem FiniteTrace.initial_not_mem_backwardVertices_of_firstForward
    (Q : FiniteTrace D) (hfirst : Q.firstLink.direction = .forward) :
    Q.initial ∉ (AltPath.finite Q).directionVertices .backward := by
  intro hiBackward
  simp only [AltPath.directionVertices, AltPath.links, FiniteTrace.links,
    Set.mem_iUnion, Set.mem_range] at hiBackward
  obtain ⟨l, ⟨j, rfl⟩, hjBackward, hiJ⟩ := hiBackward
  let i : Fin (Q.lastIndex + 1) := ⟨0, Nat.zero_lt_succ _⟩
  have hiFirst : Q.link i = Q.firstLink := rfl
  have hij : i < j := by
    have hle : i.1 ≤ j.1 := Nat.zero_le _
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · have hijEq : i = j := Fin.ext heq
      subst j
      rw [hiFirst, hfirst] at hjBackward
      cases hjBackward
  have hcompat := Q.compatible i j hij
  simp only [hiFirst, hfirst, hjBackward, CompatibleInOrder] at hcompat
  by_cases hadj : j.1 = i.1 + 1
  · have hinter : Q.initial ∈
        Q.firstLink.path.support ∩ (Q.link j).path.support :=
      ⟨Q.firstLink.entry_mem_support, hiJ⟩
    rw [hcompat.1 hadj] at hinter
    have heq : Q.initial = Q.firstLink.exit := by simpa using hinter
    exact Q.firstLink.entry_ne_exit heq
  · exact Set.disjoint_left.1 (hcompat.2 hadj)
      Q.firstLink.entry_mem_support hiJ

end Alternating

namespace DWeb.KappaLadder

open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A terminal-relaxed decoded exchange ending at a concrete target marker
is a terminal-contact switch.  Legality supplies the exact endpoint
dichotomy: the marker component is either isolated or carries the old
outgoing edge. -/
theorem terminalContactSwitching_of_targetMarker
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {Q : Alternating.FiniteTrace Gamma.graph} {y : V}
    (hQ : PopularAuxiliary.Input.IsTerminalRelaxedAlternating
      Gamma (L.popularAuxiliaryInput hlegal).ladder.paths (.finite Q))
    (hterminal : Q.terminal = y)
    (hyTarget : y ∈
      (L.popularAuxiliaryInput hlegal).targetMarkers)
    (hnoForward : ∀ z,
      (y, z) ∉ (Alternating.AltPath.finite Q).directionEdges .forward) :
    Alternating.IsTerminalContactSwitching
      (L.popularAuxiliaryInput hlegal).ladder.paths Q y := by
  have hyInitial :=
    L.targetMarker_mem_initialSet_popularAuxiliary_ladder hlegal hyTarget
  have hyEndpoint :=
    L.targetMarker_isolated_or_hasOutgoing_familyEdges hlegal hyTarget
  have hnoOutgoing : ¬ Alternating.HasOutgoing
      ((Alternating.AltPath.finite Q).directionEdges .forward) y := by
    rintro ⟨z, hyz⟩
    exact hnoForward z hyz
  rcases hyEndpoint with hyIsolated | hyOutgoing
  · exact Alternating.IsTerminalContactSwitching.of_terminalRelaxed_isolated
      hQ hterminal hyInitial hyIsolated hnoOutgoing
  · exact Alternating.IsTerminalContactSwitching.of_terminalRelaxed
      hQ hterminal hyInitial hyOutgoing hnoOutgoing

/-- Backward-first form of the bridge.  It asks only for the four internal
terminal-relaxed geometry fields; the source-end condition follows
formally because the displayed first link is backward.  This is the exact
consumer for the backward branch of a finite-source exchange. -/
theorem terminalContactSwitching_of_targetMarker_of_firstBackward
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {Q : Alternating.FiniteTrace Gamma.graph} {y : V}
    (hwarp : Gamma.IsWarp
      (L.popularAuxiliaryInput hlegal).ladder.paths)
    (hback : Alternating.BackwardLinksOn
      (L.popularAuxiliaryInput hlegal).ladder.paths (.finite Q))
    (hoff : Alternating.ForwardLinksOff
      (L.popularAuxiliaryInput hlegal).ladder.paths (.finite Q))
    (hcontacts : PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
      Gamma (L.popularAuxiliaryInput hlegal).ladder.paths (.finite Q))
    (hfirst : Q.firstLink.direction = .backward)
    (hterminal : Q.terminal = y)
    (hyTarget : y ∈
      (L.popularAuxiliaryInput hlegal).targetMarkers)
    (hnoForward : ∀ z,
      (y, z) ∉ (Alternating.AltPath.finite Q).directionEdges .forward) :
    Alternating.IsTerminalContactSwitching
      (L.popularAuxiliaryInput hlegal).ladder.paths Q y := by
  apply L.terminalContactSwitching_of_targetMarker hlegal
    (hterminal := hterminal) (hyTarget := hyTarget)
    (hnoForward := hnoForward)
  refine ⟨hwarp, hback, hoff, hcontacts, ?_⟩
  intro hforward
  have hcontra : Alternating.Direction.backward = .forward :=
    Option.some.inj (by
      simpa only [Alternating.AltPath.firstDirection?, hfirst] using hforward)
  cases hcontra

/-- Contact coverage eliminates the forward-first failure whenever the
initial and terminal endpoints are distinct: a forward first link puts the
initial vertex on the forward side, while finite-trace compatibility
prevents it from appearing on any backward link. -/
theorem terminalContactSwitching_of_targetMarker_of_distinct
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {Q : Alternating.FiniteTrace Gamma.graph} {y : V}
    (hwarp : Gamma.IsWarp
      (L.popularAuxiliaryInput hlegal).ladder.paths)
    (hback : Alternating.BackwardLinksOn
      (L.popularAuxiliaryInput hlegal).ladder.paths (.finite Q))
    (hoff : Alternating.ForwardLinksOff
      (L.popularAuxiliaryInput hlegal).ladder.paths (.finite Q))
    (hcontacts : PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
      Gamma (L.popularAuxiliaryInput hlegal).ladder.paths (.finite Q))
    (hinitial : Q.initial ∈ Gamma.vertexSet
      (L.popularAuxiliaryInput hlegal).ladder.paths)
    (hne : Q.initial ≠ y)
    (hterminal : Q.terminal = y)
    (hyTarget : y ∈
      (L.popularAuxiliaryInput hlegal).targetMarkers)
    (hnoForward : ∀ z,
      (y, z) ∉ (Alternating.AltPath.finite Q).directionEdges .forward) :
    Alternating.IsTerminalContactSwitching
      (L.popularAuxiliaryInput hlegal).ladder.paths Q y := by
  have hfirst : Q.firstLink.direction = .backward := by
    cases hdir : Q.firstLink.direction with
    | backward => rfl
    | forward =>
        exfalso
        have hiForward : Q.initial ∈
            (Alternating.AltPath.finite Q).directionVertices .forward := by
          simp only [Alternating.AltPath.directionVertices,
            Alternating.AltPath.links, Alternating.FiniteTrace.links,
            Set.mem_iUnion, Set.mem_range]
          exact ⟨Q.firstLink, ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩,
            hdir, Q.firstLink.entry_mem_support⟩
        rcases hcontacts hiForward hinitial with hiBackward | hiTerminal
        · exact
            (Q.initial_not_mem_backwardVertices_of_firstForward hdir)
              hiBackward
        · apply hne
          have hQi : Q.initial = Q.terminal :=
            (Option.some.inj hiTerminal).symm
          exact hQi.trans hterminal
  exact L.terminalContactSwitching_of_targetMarker_of_firstBackward
    hlegal hwarp hback hoff hcontacts hfirst hterminal hyTarget hnoForward

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.terminalContactSwitching_of_targetMarker
#print axioms
  Erdos599.DWeb.KappaLadder.terminalContactSwitching_of_targetMarker_of_firstBackward
#print axioms
  Erdos599.DWeb.KappaLadder.terminalContactSwitching_of_targetMarker_of_distinct
