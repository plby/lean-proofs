/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TerminalContactSwitch

/-!
# Geometry-only terminal-contact normalization

The terminal-contact shell does not depend on ordinary ladder legality.
It only needs an actual reference warp and an endpoint in its initial set.
This file records that representation-independent form, so split-legal
grounding can normalize a private finite exchange without coercing the
ladder to the legacy legality predicate.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The two genuine internal failures left after the endpoint geometry of a
finite terminal-contact trace has been discharged. -/
inductive TerminalContactGeometryOutcome
    (Z : Set Gamma.DPath) (Q : FiniteTrace Gamma.graph) (y : V) : Prop
  | switching (h : IsTerminalContactSwitching Z Q y)
  | forwardUsesReferenceEdge (h : ¬ ForwardLinksOff Z (.finite Q))
  | uncoveredForwardContact
      (h : ¬ PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
        Gamma Z (.finite Q))

private theorem walk_eq_nil_of_isPath
    {D : Digraph V} {x : V} (p : Walk D x x) (hp : p.IsPath) :
    p = .nil := by
  cases p with
  | nil => rfl
  | @cons _ y _ _ q =>
      exact False.elim ((List.nodup_cons.mp hp).1 q.end_mem_support)

private theorem finitePath_eq_trivial_of_start_eq_finish
    {D : Digraph V} (p : FinitePath D) (h : p.start = p.finish) :
    p = FinitePath.trivial D p.start := by
  rcases p with ⟨start, finish, walk, isPath⟩
  dsimp at h ⊢
  subst finish
  have hw : walk = .nil := walk_eq_nil_of_isPath walk isPath
  subst walk
  rfl

/-- A forward first link cannot revisit its initial vertex on a later
backward link of the same compatible finite trace. -/
theorem FiniteTrace.initial_not_mem_backwardVertices_of_firstForward
    (Q : FiniteTrace Gamma.graph)
    (hfirst : Q.firstLink.direction = .forward) :
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

/-- Any initial point of an arbitrary warp is either an isolated singleton
component or has an outgoing family edge. -/
theorem initialSet_mem_isolated_or_hasOutgoing
    {Z : Set Gamma.DPath} (hZ : Gamma.IsWarp Z) {y : V}
    (hy : y ∈ Gamma.initialSet Z) :
    y ∈ isolatedVertices Z ∨ HasOutgoing (familyEdges Z) y := by
  obtain ⟨p, hp, hpInitial⟩ := hy
  rw [← hpInitial]
  rcases p with p | r
  · by_cases htrivial : p.start = p.finish
    · left
      have hpEq : (Sum.inl p : Gamma.DPath) =
          Gamma.trivialPath p.start := by
        rw [finitePath_eq_trivial_of_start_eq_finish p htrivial]
        rfl
      exact hpEq ▸ hp
    · right
      obtain ⟨z, hz⟩ :=
        FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          p p.start_mem_support htrivial
      exact ⟨z, Set.mem_iUnion.2 ⟨(Sum.inl p : Gamma.DPath),
        Set.mem_iUnion.2 ⟨hp, hz⟩⟩⟩
  · right
    exact ⟨r 1, Set.mem_iUnion.2 ⟨(Sum.inr r : Gamma.DPath),
      Set.mem_iUnion.2 ⟨hp, ⟨0, rfl⟩⟩⟩⟩

/-- The representation-independent terminal-contact bridge.  Distinct
initial and terminal endpoints rule out a forward first link once all
nonterminal forward contacts are covered. -/
theorem terminalContactSwitching_of_initialSet_of_distinct
    {Z : Set Gamma.DPath} {Q : FiniteTrace Gamma.graph} {y : V}
    (hwarp : Gamma.IsWarp Z)
    (hback : BackwardLinksOn Z (.finite Q))
    (hoff : ForwardLinksOff Z (.finite Q))
    (hcontacts : PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
      Gamma Z (.finite Q))
    (hinitial : Q.initial ∈ Gamma.vertexSet Z)
    (hyInitial : y ∈ Gamma.initialSet Z)
    (hne : Q.initial ≠ y)
    (hterminal : Q.terminal = y)
    (hnoForward : ∀ z,
      (y, z) ∉ (AltPath.finite Q).directionEdges .forward) :
    IsTerminalContactSwitching Z Q y := by
  have hfirst : Q.firstLink.direction = .backward := by
    cases hdir : Q.firstLink.direction with
    | backward => rfl
    | forward =>
        exfalso
        have hiForward : Q.initial ∈
            (AltPath.finite Q).directionVertices .forward := by
          simp only [AltPath.directionVertices, AltPath.links,
            FiniteTrace.links, Set.mem_iUnion, Set.mem_range]
          exact ⟨Q.firstLink, ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩,
            hdir, Q.firstLink.entry_mem_support⟩
        rcases hcontacts hiForward hinitial with hiBackward | hiTerminal
        · exact (Q.initial_not_mem_backwardVertices_of_firstForward hdir)
            hiBackward
        · apply hne
          have hQi : Q.initial = Q.terminal :=
            (Option.some.inj hiTerminal).symm
          exact hQi.trans hterminal
  have hrelaxed :
      PopularAuxiliary.Input.IsTerminalRelaxedAlternating
        Gamma Z (.finite Q) := by
    refine ⟨hwarp, hback, hoff, hcontacts, ?_⟩
    intro hforward
    have hcontra : Direction.backward = .forward :=
      Option.some.inj (by
        simpa only [AltPath.firstDirection?, hfirst] using hforward)
    cases hcontra
  have hnoOutgoing : ¬ HasOutgoing
      ((AltPath.finite Q).directionEdges .forward) y := by
    rintro ⟨z, hyz⟩
    exact hnoForward z hyz
  rcases initialSet_mem_isolated_or_hasOutgoing hwarp hyInitial with
      hyIsolated | hyOutgoing
  · exact IsTerminalContactSwitching.of_terminalRelaxed_isolated
      hrelaxed hterminal hyInitial hyIsolated hnoOutgoing
  · exact IsTerminalContactSwitching.of_terminalRelaxed
      hrelaxed hterminal hyInitial hyOutgoing hnoOutgoing

/-- Total terminal normalization using only explicit reference-warp
geometry. -/
theorem finiteSourceTerminalOutcome_of_geometry
    {Z : Set Gamma.DPath} {Q : FiniteTrace Gamma.graph} {y : V}
    (hwarp : Gamma.IsWarp Z)
    (hback : BackwardLinksOn Z (.finite Q))
    (hinitial : Q.initial ∈ Gamma.vertexSet Z)
    (hyInitial : y ∈ Gamma.initialSet Z)
    (hne : Q.initial ≠ y)
    (hterminal : Q.terminal = y)
    (hnoForward : ∀ z,
      (y, z) ∉ (AltPath.finite Q).directionEdges .forward) :
    TerminalContactGeometryOutcome Z Q y := by
  by_cases hoff : ForwardLinksOff Z (.finite Q)
  · by_cases hcontacts :
        PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
          Gamma Z (.finite Q)
    · exact .switching <|
        terminalContactSwitching_of_initialSet_of_distinct hwarp hback hoff
          hcontacts hinitial hyInitial hne hterminal hnoForward
    · exact .uncoveredForwardContact hcontacts
  · exact .forwardUsesReferenceEdge hoff

end Alternating
end Erdos599

#print axioms Erdos599.Alternating.initialSet_mem_isolated_or_hasOutgoing
#print axioms
  Erdos599.Alternating.terminalContactSwitching_of_initialSet_of_distinct
#print axioms Erdos599.Alternating.finiteSourceTerminalOutcome_of_geometry
