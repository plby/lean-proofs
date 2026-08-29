/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureTerminalReduction

/-!
# Activated reference-prefix endpoints enter the later interval

An activated reference prefix ends on the old/current frontier and lies in
the moving closed set.  Unless that endpoint is already on the captured
later frontier, the complete later interval has a genuine outgoing edge
there.  If its head remains closed, this edge is retained literally by the
inside restriction.  Otherwise the endpoint is exactly an uncovered source
of the fractured assignment.

Thus a terminal at an activated-prefix endpoint can only be caused by the
first contact transition of the assignment being omitted; it is not a gap in
the interval row or in root reachability.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- Every activated-prefix terminal belongs to the moving closed set. -/
theorem activatedPrefix_terminal_mem_closedSet
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {x : V}
    (hx : x ∈ Gamma.terminalFrontier
      (activatedReferencePrefixes C current Rlimit.closedSet)) :
    x ∈ Rlimit.closedSet := by
  obtain ⟨p, hp, hpTerminal⟩ := hx
  exact activatedReferencePrefixes.support_subset Rlimit.reference_closed hp
    ((Gamma.terminal_mem_support hpTerminal))

/-- Away from the captured frontier, the actual later interval has an
outgoing edge at every activated-prefix endpoint. -/
theorem exists_intervalEdge_of_activatedPrefix_terminal_not_captured
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {x : V}
    (hx : x ∈ Gamma.terminalFrontier
      (activatedReferencePrefixes C current Rlimit.closedSet))
    (hxNotCaptured : x ∉ Rlimit.capturedGeometry.newSlice) :
    ∃ y, (x, y) ∈ familyEdges T.interval.ambientInterval := by
  have hxOld : x ∈ C.newSlice :=
    activatedReferencePrefixes.terminalFrontier_subset_currentSlice hx
  have hxInitial : x ∈ Gamma.initialSet T.interval.ambientInterval := by
    rw [T.interval.ambientInterval_linkage.initialSet_eq]
    simpa only [DynamicMoving931GlobalClosure.capturedGeometry_oldSlice] using
      hxOld
  have hxVertex : x ∈ Gamma.vertexSet T.interval.ambientInterval := by
    obtain ⟨p, hp, hpInitial⟩ := hxInitial
    exact ⟨p, hp, hpInitial.symm ▸ p.initial_mem_support⟩
  have hxNotTerminal : x ∉
      Gamma.terminalFrontier T.interval.ambientInterval := by
    intro hxTerminal
    exact hxNotCaptured
      (T.interval.ambientInterval_linkage.terminalFrontier_subset hxTerminal)
  by_contra hno
  apply hxNotTerminal
  rw [isWarp_terminalFrontier_eq_noOutgoing
    T.interval.ambientInterval_linkage.isWarp]
  exact ⟨hxVertex, hno⟩

/-- A closed cut exit is an initial of the literal outside-fragment family. -/
theorem mem_holeInitial_of_mem_closedSet_of_intervalEdge_leaving
    (M : PostClosureMacroCompressorAssignment T)
    {x y : V} (hxClosed : x ∈ Rlimit.closedSet)
    (hyNotClosed : y ∉ Rlimit.closedSet)
    (hxy : (x, y) ∈ familyEdges T.interval.ambientInterval) :
    x ∈ Gamma.initialSet M.fractured.outside.holes.paths := by
  rw [M.fractured.outside.initialSet_eq]
  left
  refine ⟨hxClosed, y, hxy, ?_⟩
  rintro ⟨_hx, hy⟩
  exact hyNotClosed hy

/-- No outside-reference member can start at a vertex already in the closed
set, because every such member is disjoint from that set. -/
theorem not_mem_outsideReference_initialSet_of_mem_closedSet
    {x : V} (hxClosed : x ∈ Rlimit.closedSet) :
    x ∉ Gamma.initialSet
      (outsideReference T.intervalReference Rlimit.closedSet) := by
  rintro ⟨p, hp, hpInitial⟩
  exact Set.disjoint_left.1 hp.2
    (by simpa only [hpInitial] using p.initial_mem_support) hxClosed

/-- Exact activated-prefix boundary trichotomy.  The final alternative is
the actual source type used by the post-closure compressor assignment. -/
theorem activatedPrefix_terminal_captured_or_insideOutgoing_or_assignmentSource
    (M : PostClosureMacroCompressorAssignment T)
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {x : V}
    (hx : x ∈ Gamma.terminalFrontier
      (activatedReferencePrefixes C current Rlimit.closedSet)) :
    x ∈ Rlimit.capturedGeometry.newSlice ∨
      (∃ y, (x, y) ∈ sourceInsideEdges
        T.interval.ambientInterval Rlimit.closedSet) ∨
      x ∈ Gamma.initialSet M.fractured.outside.holes.paths \
        Gamma.initialSet
          (outsideReference T.intervalReference Rlimit.closedSet) := by
  by_cases hxCaptured : x ∈ Rlimit.capturedGeometry.newSlice
  · exact Or.inl hxCaptured
  · right
    obtain ⟨y, hxy⟩ :=
      exists_intervalEdge_of_activatedPrefix_terminal_not_captured
        current hx hxCaptured
    have hxClosed : x ∈ Rlimit.closedSet :=
      activatedPrefix_terminal_mem_closedSet current hx
    by_cases hyClosed : y ∈ Rlimit.closedSet
    · left
      exact ⟨y, hxy, hxClosed, hyClosed⟩
    · right
      exact ⟨M.mem_holeInitial_of_mem_closedSet_of_intervalEdge_leaving
          hxClosed hyClosed hxy,
        not_mem_outsideReference_initialSet_of_mem_closedSet hxClosed⟩

#print axioms activatedPrefix_terminal_mem_closedSet
#print axioms exists_intervalEdge_of_activatedPrefix_terminal_not_captured
#print axioms
  activatedPrefix_terminal_captured_or_insideOutgoing_or_assignmentSource

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
