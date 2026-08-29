/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureActivatedPrefixExit

/-!
# Terminal boundary reduced to actual assignment sources

Every endpoint of an actual closed edge lies on the later interval row.  At
a closed interval vertex with no outgoing closed edge, either the row has
already reached its captured-frontier terminal or its next edge exits the
closed set.  In the latter case the vertex is exactly an uncovered source of
the fractured assignment.

Combining this with the activated-prefix analysis reduces every unresolved
terminal of the concrete pre-tail blueprint to one source-indexed transition
of the actual assignment.
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

/-- The actual source set indexing the post-closure assignment. -/
def actualPostClosureAssignmentSources
    (M : PostClosureMacroCompressorAssignment T) : Set V :=
  Gamma.initialSet M.fractured.outside.holes.paths \
    Gamma.initialSet
      (outsideReference T.intervalReference Rlimit.closedSet)

/-- Every actual assignment source was absorbed by the moving closure. -/
theorem assignmentSource_mem_closedSet
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    x ∈ Rlimit.closedSet := by
  exact T.uncovered_initials_subset_closedSet Rlimit M.fractured hx

/-- Every actual assignment source is a genuine cut exit and hence is
nonpersistent. -/
theorem assignmentSource_not_mem_persistent
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    x ∉ C.persistent := by
  have hxClosed : x ∈ Rlimit.closedSet := M.assignmentSource_mem_closedSet hx
  have hxCut : x ∈ CutSplit.initialVertices
      (outsideCarrier T.interval.ambientInterval Rlimit.closedSet)
      (outsideFamilyEdges T.interval.ambientInterval Rlimit.closedSet)
      Rlimit.closedSet := by
    have hxInitial := hx.1
    rw [M.fractured.outside.initialSet_eq] at hxInitial
    exact hxInitial
  exact T.not_mem_persistent_of_mem_cutInitial_inter_closedSet
    Rlimit ⟨hxCut, hxClosed⟩

/-- In particular an actual assignment source is not already on the captured
later frontier.  It must receive an outgoing transition or be certified
popular. -/
theorem assignmentSource_not_mem_capturedSlice
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureAssignmentSources) :
    x ∉ Rlimit.capturedGeometry.newSlice := by
  intro hxCaptured
  have hxClosed : x ∈ Rlimit.closedSet := M.assignmentSource_mem_closedSet hx
  have hpair : x ∈
      Rlimit.closedSet ∩ C.ladder.frontier Rlimit.later.stage := by
    refine ⟨hxClosed, ?_⟩
    simpa only [DynamicMoving931GlobalClosure.capturedGeometry_newSlice] using
      hxCaptured
  rw [Rlimit.frontier_inter] at hpair
  exact M.assignmentSource_not_mem_persistent hx hpair.2

/-- A closed interval-row vertex at which no actual closed edge leaves is
either a captured terminal or an actual assignment source. -/
theorem captured_or_assignmentSource_of_closed_interval_deadEnd
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hxClosed : x ∈ Rlimit.closedSet)
    (hxRow : x ∈ Gamma.vertexSet T.interval.ambientInterval)
    (hno : ¬ ∃ y, (x, y) ∈
      M.toPostClosureCompressorAssignment.actualPostClosureClosedEdges) :
    x ∈ Rlimit.capturedGeometry.newSlice ∨
      x ∈ M.actualPostClosureAssignmentSources := by
  by_cases hxTerminal : x ∈
      Gamma.terminalFrontier T.interval.ambientInterval
  · left
    exact T.interval.ambientInterval_linkage.terminalFrontier_subset hxTerminal
  · right
    have hout : ∃ y, (x, y) ∈ familyEdges T.interval.ambientInterval := by
      by_contra hnone
      apply hxTerminal
      rw [isWarp_terminalFrontier_eq_noOutgoing
        T.interval.ambientInterval_linkage.isWarp]
      exact ⟨hxRow, hnone⟩
    obtain ⟨y, hxy⟩ := hout
    by_cases hyClosed : y ∈ Rlimit.closedSet
    · exact False.elim (hno ⟨y, Or.inl ⟨hxy, hxClosed, hyClosed⟩⟩)
    · exact ⟨M.mem_holeInitial_of_mem_closedSet_of_intervalEdge_leaving
          hxClosed hyClosed hxy,
        not_mem_outsideReference_initialSet_of_mem_closedSet hxClosed⟩

/-- Every reached fresh dead end is therefore captured or is an actual
assignment source. -/
theorem freshDeadEnd_captured_or_assignmentSource
    (M : PostClosureMacroCompressorAssignment T)
    {x : V} (hx : x ∈ M.actualPostClosureFreshDeadEnds) :
    x ∈ Rlimit.capturedGeometry.newSlice ∨
      x ∈ M.actualPostClosureAssignmentSources := by
  obtain ⟨⟨a, hax⟩, hno⟩ := hx
  have hendClosed := M.toPostClosureCompressorAssignment
    |>.actualPostClosureClosedEdges_endpoints_closed hax
  have hendRow := M.actualPostClosureClosedEdges_endpoints_ambientInterval hax
  exact M.captured_or_assignmentSource_of_closed_interval_deadEnd
    hendClosed.2 hendRow.2 hno

/-- A terminal of the root-reachable output which is an activated-prefix
endpoint is captured unless it is itself an actual assignment source. -/
theorem prefixTerminal_captured_or_assignmentSource
    (M : PostClosureMacroCompressorAssignment T)
    (current A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hAU : A.OrdinaryExtends U)
    (hUE : U.edgeSet = RootReachableRelation.edges
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hUV : U.vertexSet = RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet)
    {x : V} (hxTerminal : x ∈ U.terminalSet)
    (hxPrefix : x ∈ Gamma.terminalFrontier
      (activatedReferencePrefixes C current Rlimit.closedSet)) :
    x ∈ Rlimit.capturedGeometry.newSlice ∨
      x ∈ M.actualPostClosureAssignmentSources := by
  have hno := M.terminal_noOutgoing_actualPostClosureClosedEdges
    A U hAU hUE hUV hxTerminal
  rcases M.activatedPrefix_terminal_captured_or_insideOutgoing_or_assignmentSource
      current hxPrefix with hxCaptured | hxInside | hxSource
  · exact Or.inl hxCaptured
  · exact False.elim (hno ⟨hxInside.choose, Or.inl hxInside.choose_spec⟩)
  · exact Or.inr hxSource

/-- Final pre-tail terminal reduction: inherited terminals are popular or
captured, and every remaining terminal is indexed by the actual fractured
assignment. -/
theorem terminals_subset_popular_union_captured_union_assignmentSources
    (M : PostClosureMacroCompressorAssignment T)
    (current A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hstable : current.Stable C.newSlice C.persistent)
    (hseed : current.terminalSet ∩ C.newSlice ⊆ seed)
    (hcurrentA : current.OrdinaryExtends A)
    (hAU : A.OrdinaryExtends U)
    (hAE : A.edgeSet =
      referencePrefixSeedEdges current Rlimit.closedSet)
    (hAV : A.vertexSet = current.vertexSet ∪ Gamma.vertexSet
      (activatedReferencePrefixes C current Rlimit.closedSet))
    (hUE : U.edgeSet = RootReachableRelation.edges
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hUV : U.vertexSet = RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet) :
    U.terminalSet ⊆
      ({x | IsPopular Gamma C.ladder.limitWarp C.persistent kappa x} ∪
        Rlimit.capturedGeometry.newSlice) ∪
          M.actualPostClosureAssignmentSources := by
  intro x hx
  rcases M.terminal_mem_current_or_prefixTerminal_or_freshDeadEnd
      current A U hcurrentA hAU hAE hAV hUE hUV hx with
    hxCurrent | hxPrefix | hxFresh
  · left
    exact current_terminal_popular_or_captured current hcurrent hstable hseed
      hxCurrent
  · rcases M.prefixTerminal_captured_or_assignmentSource
        current A U hAU hUE hUV hx hxPrefix with hxCaptured | hxSource
    · exact Or.inl (Or.inr hxCaptured)
    · exact Or.inr hxSource
  · rcases M.freshDeadEnd_captured_or_assignmentSource hxFresh with
      hxCaptured | hxSource
    · exact Or.inl (Or.inr hxCaptured)
    · exact Or.inr hxSource

/-- Fair-facing exact discharge form.  It is enough to prove that an actual
assignment source with no outgoing closed transition is popular.  Every
other terminal has already been handled by inherited stability or the
captured frontier. -/
theorem terminals_popular_of_assignmentSource_deadEnds_popular
    (M : PostClosureMacroCompressorAssignment T)
    (current A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hstable : current.Stable C.newSlice C.persistent)
    (hseed : current.terminalSet ∩ C.newSlice ⊆ seed)
    (hcurrentA : current.OrdinaryExtends A)
    (hAU : A.OrdinaryExtends U)
    (hAE : A.edgeSet =
      referencePrefixSeedEdges current Rlimit.closedSet)
    (hAV : A.vertexSet = current.vertexSet ∪ Gamma.vertexSet
      (activatedReferencePrefixes C current Rlimit.closedSet))
    (hUE : U.edgeSet = RootReachableRelation.edges
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hUV : U.vertexSet = RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hsource : ∀ x, x ∈ M.actualPostClosureAssignmentSources →
      (¬ ∃ y, (x, y) ∈
        M.toPostClosureCompressorAssignment.actualPostClosureClosedEdges) →
      IsPopular Gamma C.ladder.limitWarp C.persistent kappa x) :
    U.terminalSet ⊆
      {x | IsPopular Gamma C.ladder.limitWarp C.persistent kappa x} ∪
        Rlimit.capturedGeometry.newSlice := by
  intro x hx
  rcases M.terminals_subset_popular_union_captured_union_assignmentSources
      current A U hcurrent hstable hseed hcurrentA hAU hAE hAV hUE hUV hx with
    hxBoundary | hxSource
  · exact hxBoundary
  · left
    exact hsource x hxSource
      (M.terminal_noOutgoing_actualPostClosureClosedEdges
        A U hAU hUE hUV hx)

#print axioms captured_or_assignmentSource_of_closed_interval_deadEnd
#print axioms assignmentSource_not_mem_persistent
#print axioms assignmentSource_not_mem_capturedSlice
#print axioms freshDeadEnd_captured_or_assignmentSource
#print axioms prefixTerminal_captured_or_assignmentSource
#print axioms
  terminals_subset_popular_union_captured_union_assignmentSources
#print axioms terminals_popular_of_assignmentSource_deadEnds_popular

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
