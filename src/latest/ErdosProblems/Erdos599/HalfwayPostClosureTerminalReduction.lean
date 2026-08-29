/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureTargetTailBoundary
import ErdosProblems.Erdos599.HalfwayPostClosurePrefixedStability

/-!
# Exact terminal reduction for the post-closure attachment

Root-reachable restriction creates no artificial sink at a reachable
vertex: it keeps every available outgoing edge.  Hence a terminal of the
actual prefixed attachment is either already a terminal of the current
blueprint, or is a closed vertex at which the complete inside-plus-shortcut
relation has no outgoing edge.  Current terminals are popular or are moved
to the captured frontier by the stability seed.

This isolates the genuine remaining boundary problem without classifying an
endpoint-covered contact by assumption.
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

/-- Closed vertices at which the actual inside-plus-shortcut relation has no
successor.  These, and only these, are the possible new sinks after all
inherited current edges have been retained. -/
def actualPostClosureClosedDeadEnds
    (M : PostClosureMacroCompressorAssignment T) : Set V :=
  {x | x ∈ Rlimit.closedSet ∧
    ¬ ∃ y, (x, y) ∈
      M.toPostClosureCompressorAssignment.actualPostClosureClosedEdges}

/-- A new dead end actually reached through the fresh closed relation.  This
excludes irrelevant vertices of the closing set and is the precise target of
the contact-boundary classification. -/
def actualPostClosureFreshDeadEnds
    (M : PostClosureMacroCompressorAssignment T) : Set V :=
  {x | (∃ a, (a, x) ∈
      M.toPostClosureCompressorAssignment.actualPostClosureClosedEdges) ∧
    ¬ ∃ y, (x, y) ∈
      M.toPostClosureCompressorAssignment.actualPostClosureClosedEdges}

/-- At a terminal of the root-reachable attachment, no edge of the complete
closed fresh relation can leave.  The old-priority filter discards a fresh
edge only when an old edge already leaves, and either edge would survive the
root-reachable restriction. -/
theorem terminal_noOutgoing_actualPostClosureClosedEdges
    (M : PostClosureMacroCompressorAssignment T)
    (A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hAU : A.OrdinaryExtends U)
    (hUE : U.edgeSet = RootReachableRelation.edges
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hUV : U.vertexSet = RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet)
    {x : V} (hxTerminal : x ∈ U.terminalSet) :
    ¬ ∃ y, (x, y) ∈
      M.toPostClosureCompressorAssignment.actualPostClosureClosedEdges := by
  have hxU : x ∈ U.vertexSet := by
    obtain ⟨p, hp, hpTerminal⟩ := hxTerminal
    exact ⟨p, hp,
      (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminal_mem_support
        hpTerminal⟩
  have hnoU : ¬ ∃ y, (x, y) ∈ U.edgeSet :=
    isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier U.isWarp hxTerminal
  have hnoA : ¬ ∃ y, (x, y) ∈ A.edgeSet := by
    rintro ⟨y, hxy⟩
    exact hnoU ⟨y, hAU.edges_mono hxy⟩
  have hxReachable : x ∈ RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet := by
    rw [← hUV]
    exact hxU
  rintro ⟨y, hxyClosed⟩
  have hxyFresh : (x, y) ∈ M.oldPriorityFreshEdges A :=
    ⟨hxyClosed, hnoA⟩
  apply hnoU
  refine ⟨y, ?_⟩
  rw [hUE]
  exact ⟨Or.inr hxyFresh, hxReachable⟩

/-- Every terminal of the concrete prefixed root-reachable attachment is
either inherited from the current blueprint or is an exact dead end of the
closed fresh relation. -/
theorem terminal_mem_current_or_closedDeadEnd
    (M : PostClosureMacroCompressorAssignment T)
    (current A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hcurrentA : current.OrdinaryExtends A)
    (hAU : A.OrdinaryExtends U)
    (hUE : U.edgeSet = RootReachableRelation.edges
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hUV : U.vertexSet = RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hcarrier : U.vertexSet ⊆ current.vertexSet ∪ Rlimit.closedSet)
    {x : V} (hxTerminal : x ∈ U.terminalSet) :
    x ∈ current.terminalSet ∨ x ∈ M.actualPostClosureClosedDeadEnds := by
  have hxU : x ∈ U.vertexSet := by
    obtain ⟨p, hp, hpTerminal⟩ := hxTerminal
    exact ⟨p, hp,
      (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminal_mem_support
        hpTerminal⟩
  have hnoU : ¬ ∃ y, (x, y) ∈ U.edgeSet :=
    isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier U.isWarp hxTerminal
  rcases hcarrier hxU with hxCurrent | hxClosed
  · left
    change x ∈
      (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminalFrontier
        current.paths
    rw [isWarp_terminalFrontier_eq_noOutgoing current.isWarp]
    refine ⟨hxCurrent, ?_⟩
    rintro ⟨y, hxy⟩
    exact hnoU ⟨y, hAU.edges_mono (hcurrentA.edges_mono hxy)⟩
  · right
    refine ⟨hxClosed, ?_⟩
    rintro ⟨y, hxyClosed⟩
    have hnoA : ¬ ∃ v, (x, v) ∈ A.edgeSet := by
      rintro ⟨v, hxv⟩
      exact hnoU ⟨v, hAU.edges_mono hxv⟩
    have hxyFresh : (x, y) ∈ M.oldPriorityFreshEdges A :=
      ⟨hxyClosed, hnoA⟩
    have hxyCandidate : (x, y) ∈ M.oldPriorityAttachedEdges A :=
      Or.inr hxyFresh
    have hxReachable : x ∈ RootReachableRelation.carrier
        (M.oldPriorityAttachedEdges A) A.initialSet := by
      rw [← hUV]
      exact hxU
    apply hnoU
    refine ⟨y, ?_⟩
    rw [hUE]
    exact ⟨hxyCandidate, hxReachable⟩

/-- The sharper boundary decomposition retaining construction provenance.
A terminal is inherited, is the endpoint of an activated reference prefix,
or is a fresh closed-relation dead end reached through an actual fresh edge.
-/
theorem terminal_mem_current_or_prefixTerminal_or_freshDeadEnd
    (M : PostClosureMacroCompressorAssignment T)
    (current A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
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
    {x : V} (hxTerminal : x ∈ U.terminalSet) :
    x ∈ current.terminalSet ∨
      x ∈ Gamma.terminalFrontier
        (activatedReferencePrefixes C current Rlimit.closedSet) ∨
      x ∈ M.actualPostClosureFreshDeadEnds := by
  have hxU : x ∈ U.vertexSet := by
    obtain ⟨p, hp, hpTerminal⟩ := hxTerminal
    exact ⟨p, hp,
      (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminal_mem_support
        hpTerminal⟩
  have hnoU : ¬ ∃ y, (x, y) ∈ U.edgeSet :=
    isWarp_noOutgoing_familyEdges_of_mem_terminalFrontier U.isWarp hxTerminal
  have hnoA : ¬ ∃ y, (x, y) ∈ A.edgeSet := by
    rintro ⟨y, hxy⟩
    exact hnoU ⟨y, hAU.edges_mono hxy⟩
  by_cases hxA : x ∈ A.vertexSet
  · rw [hAV] at hxA
    rcases hxA with hxCurrent | hxPrefix
    · left
      change x ∈
        (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminalFrontier
          current.paths
      rw [isWarp_terminalFrontier_eq_noOutgoing current.isWarp]
      refine ⟨hxCurrent, ?_⟩
      rintro ⟨y, hxy⟩
      exact hnoA ⟨y, hcurrentA.edges_mono hxy⟩
    · right; left
      rw [isWarp_terminalFrontier_eq_noOutgoing
        activatedReferencePrefixes.isWarp]
      refine ⟨hxPrefix, ?_⟩
      rintro ⟨y, hxy⟩
      apply hnoA
      refine ⟨y, ?_⟩
      rw [hAE]
      exact Or.inr hxy
  · right; right
    have hxReachable : x ∈ RootReachableRelation.carrier
        (M.oldPriorityAttachedEdges A) A.initialSet := by
      rw [← hUV]
      exact hxU
    obtain ⟨n, hn⟩ := hxReachable
    cases n with
    | zero =>
        exfalso
        apply hxA
        obtain ⟨p, hp, hpInitial⟩ := hn
        exact ⟨p, hp, hpInitial.symm ▸ p.initial_mem_support⟩
    | succ n =>
        obtain ⟨a, haReachable, hax⟩ := hn
        have haxFresh : (a, x) ∈ M.oldPriorityFreshEdges A := by
          rcases hax with haxOld | haxFresh
          · exfalso
            apply hxA
            change (a, x) ∈ familyEdges
              (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) A.paths at haxOld
            exact (familyEdges_subset_vertexSet_prod
              (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa)
              A.paths haxOld).2
          · exact haxFresh
        refine ⟨⟨a, haxFresh.1⟩, ?_⟩
        rintro ⟨y, hxyClosed⟩
        have hxyFresh : (x, y) ∈ M.oldPriorityFreshEdges A :=
          ⟨hxyClosed, hnoA⟩
        apply hnoU
        refine ⟨y, ?_⟩
        rw [hUE]
        exact ⟨Or.inr hxyFresh, ⟨n + 1, ⟨a, haReachable, hax⟩⟩⟩

/-- A current terminal is already popular, or the terminal seed and stable
capture put it on the newly captured frontier. -/
theorem current_terminal_popular_or_captured
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hstable : current.Stable C.newSlice C.persistent)
    (hseed : current.terminalSet ∩ C.newSlice ⊆ seed)
    {x : V} (hx : x ∈ current.terminalSet) :
    IsPopular Gamma C.ladder.limitWarp C.persistent kappa x ∨
      x ∈ Rlimit.capturedGeometry.newSlice := by
  rcases hcurrent.terminals_popular hx with hxPopular | hxOldSlice
  · exact Or.inl hxPopular
  · right
    have hxSeed : x ∈ seed := hseed ⟨hx, hxOldSlice⟩
    have hxClosed : x ∈ Rlimit.closedSet := Rlimit.seed_subset hxSeed
    have hxPersistent : x ∈ C.persistent :=
      hstable ⟨hx, hxOldSlice⟩
    have hpair : x ∈ Rlimit.closedSet ∩ C.persistent :=
      ⟨hxClosed, hxPersistent⟩
    rw [← Rlimit.frontier_inter] at hpair
    simpa only [DynamicMoving931GlobalClosure.capturedGeometry_newSlice] using
      hpair.2

/-- Exact terminal trichotomy for the actual pre-tail blueprint.  The third
set is the sole unresolved endpoint-covered sink obligation. -/
theorem terminals_subset_popular_union_captured_union_closedDeadEnds
    (M : PostClosureMacroCompressorAssignment T)
    (current A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hstable : current.Stable C.newSlice C.persistent)
    (hseed : current.terminalSet ∩ C.newSlice ⊆ seed)
    (hcurrentA : current.OrdinaryExtends A)
    (hAU : A.OrdinaryExtends U)
    (hUE : U.edgeSet = RootReachableRelation.edges
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hUV : U.vertexSet = RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hcarrier : U.vertexSet ⊆ current.vertexSet ∪ Rlimit.closedSet) :
    U.terminalSet ⊆
      ({x | IsPopular Gamma C.ladder.limitWarp C.persistent kappa x} ∪
        Rlimit.capturedGeometry.newSlice) ∪
          M.actualPostClosureClosedDeadEnds := by
  intro x hx
  rcases M.terminal_mem_current_or_closedDeadEnd current A U
      hcurrentA hAU hUE hUV hcarrier hx with hxCurrent | hxDead
  · left
    exact current_terminal_popular_or_captured current hcurrent hstable hseed
      hxCurrent
  · exact Or.inr hxDead

#print axioms terminal_mem_current_or_closedDeadEnd
#print axioms terminal_noOutgoing_actualPostClosureClosedEdges
#print axioms terminal_mem_current_or_prefixTerminal_or_freshDeadEnd
#print axioms current_terminal_popular_or_captured
#print axioms terminals_subset_popular_union_captured_union_closedDeadEnds

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
