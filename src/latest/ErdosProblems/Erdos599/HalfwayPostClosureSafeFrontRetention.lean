/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosurePrefixedAttachment

/-!
# Retention of the scheduled safe front

The old-priority attachment must not discard the designated path.  Its
current-to-captured-frontier prefix lies in the literal ambient interval and
was seeded into the closing set.  At its initial vertex the current path is
terminal; every later tail vertex has an incoming interval edge and therefore
lies outside the old roof.  Hence none of the prefix edges is removed by the
old-outgoing priority filter.
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

private theorem safe_path_mem
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    (Sum.inl T.interval.path : Gamma.DPath) ∈ T.safe.ambientFamily := by
  have h := T.interval.path_mem_safe
  rw [T.interval_safe_eq] at h
  exact h

theorem front_support_subset_closedSet
    (T : PostClosureIntervalTransaction C globalZ seed z
      Rlimit.toDynamicMoving931GlobalClosure) :
    T.interval.front.support ⊆ Rlimit.closedSet := by
  intro x hx
  apply T.safe_vertices_closed
  exact ⟨.inl T.interval.path, safe_path_mem T,
    T.interval.front_support_subset_path hx⟩

theorem front_edgeSet_subset_closedEdges
    (M : PostClosureMacroCompressorAssignment T) :
    T.interval.front.edgeSet ⊆
      M.toPostClosureCompressorAssignment.actualPostClosureClosedEdges := by
  intro e he
  left
  refine ⟨?_, front_support_subset_closedSet T
    (T.interval.front.edgeSet_subset_support_prod he).1,
      front_support_subset_closedSet T
        (T.interval.front.edgeSet_subset_support_prod he).2⟩
  exact Set.mem_iUnion.2 ⟨.inl T.interval.front,
    Set.mem_iUnion.2 ⟨T.interval.front_mem_interval, he⟩⟩

/-- A terminal of the current blueprint has no outgoing current edge. -/
theorem current_terminal_noOutgoing
    (current : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {x : V} (hx : x ∈ current.terminalSet) :
    ¬ ∃ y, (x, y) ∈ current.edgeSet := by
  rintro ⟨y, hxy⟩
  obtain ⟨p, hp, hpTerminal⟩ := hx
  change (x, y) ∈ familyEdges
    (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) current.paths at hxy
  simp only [familyEdges, Set.mem_iUnion] at hxy
  obtain ⟨q, hq, hxyq⟩ := hxy
  have hxp : x ∈ p.support :=
    (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminal_mem_support hpTerminal
  have hpq : p = q := DWeb.IsWarp.eq_of_mem_support
    current.isWarp hp hq hxp (q.edgeSet_subset_support_prod hxyq).1
  subst q
  rcases p with p | r
  · have hpfinish : p.finish = x := by
      simpa [DWeb.terminal?, DirectedPath.Path.terminal?] using hpTerminal
    exact Alternating.FinitePath.no_outgoing_edge_at_finish p y
      (hpfinish ▸ hxyq)
  · simp [DWeb.terminal?, DirectedPath.Path.terminal?] at hpTerminal

/-- Every safe-front edge survives the old-priority filter on the exact
activated-prefix seed. -/
theorem front_edgeSet_subset_oldPriorityFreshEdges
    (M : PostClosureMacroCompressorAssignment T)
    (current A : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hzTerminal : z ∈ current.terminalSet)
    (hAE : A.edgeSet =
      referencePrefixSeedEdges current Rlimit.closedSet)
    (hAV : A.vertexSet = current.vertexSet ∪ Gamma.vertexSet
      (activatedReferencePrefixes C current Rlimit.closedSet)) :
    T.interval.front.edgeSet ⊆ M.oldPriorityFreshEdges A := by
  intro e he
  refine ⟨M.front_edgeSet_subset_closedEdges he, ?_⟩
  rintro ⟨v, hev⟩
  have hAroof : A.vertexSet ⊆ Gamma.roof C.newSlice :=
    referencePrefixSeed.blueprint_vertices_roofed hcurrent hAV
  by_cases hstart : e.1 = z
  · have hcurrentNo : ¬ ∃ v, (z, v) ∈ current.edgeSet :=
      current_terminal_noOutgoing current hzTerminal
    rw [hAE] at hev
    rcases hev with hev | hev
    · exact hcurrentNo ⟨v, hstart ▸ hev⟩
    · have hzCurrent : z ∈ current.vertexSet := by
        obtain ⟨p, hp, hpTerminal⟩ := hzTerminal
        exact ⟨p, hp,
          (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminal_mem_support
            hpTerminal⟩
      have hzPrefix : z ∈ Gamma.vertexSet
          (activatedReferencePrefixes C current Rlimit.closedSet) := by
        have hend := familyEdges_subset_vertexSet_prod
          (activatedReferencePrefixes C current Rlimit.closedSet) hev
        exact hstart ▸ hend.1
      exact Set.disjoint_left.1 referencePrefixSeed.vertexSets_disjoint
        hzCurrent hzPrefix
  · have htailSupport : e.1 ∈ T.interval.front.support :=
      (T.interval.front.edgeSet_subset_support_prod he).1
    have hneStart : e.1 ≠ T.interval.front.start := by
      rwa [T.interval.front_start]
    obtain ⟨w, hwe⟩ :=
      Alternating.FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        T.interval.front htailSupport hneStart
    have hweRow : (w, e.1) ∈ familyEdges T.interval.ambientInterval :=
      Set.mem_iUnion.2 ⟨.inl T.interval.front,
        Set.mem_iUnion.2 ⟨T.interval.front_mem_interval, hwe⟩⟩
    have hnotRoof : e.1 ∉ Gamma.roof C.newSlice :=
      T.intervalFamilyEdge_head_not_mem_currentRoof hweRow
    apply hnotRoof
    apply hAroof
    change (e.1, v) ∈ familyEdges
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) A.paths at hev
    exact (familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) A.paths hev).1

theorem front_edgeSet_subset_oldPriorityAttachedEdges
    (M : PostClosureMacroCompressorAssignment T)
    (current A : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hzTerminal : z ∈ current.terminalSet)
    (hAE : A.edgeSet =
      referencePrefixSeedEdges current Rlimit.closedSet)
    (hAV : A.vertexSet = current.vertexSet ∪ Gamma.vertexSet
      (activatedReferencePrefixes C current Rlimit.closedSet)) :
    T.interval.front.edgeSet ⊆ M.oldPriorityAttachedEdges A :=
  (M.front_edgeSet_subset_oldPriorityFreshEdges current A hcurrent
    hzTerminal hAE hAV).trans Set.subset_union_right

/-- The root-reachable restriction retains the whole safe front, not merely
its first edge, because its initial vertex already belongs to the retained
seed blueprint. -/
theorem front_edgeSet_subset_rootReachableBlueprint
    (M : PostClosureMacroCompressorAssignment T)
    (current A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hzTerminal : z ∈ current.terminalSet)
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
    T.interval.front.edgeSet ⊆ U.edgeSet := by
  let P : FinitePath (imaginaryGraph Gamma C.ladder.limitWarp kappa) :=
    LinkageBlueprint.liftOriginal T.interval.front
  let Q : (imaginaryWeb Gamma C.ladder.limitWarp kappa).DPath := .inl P
  have hQedge : Q.edgeSet = T.interval.front.edgeSet := by
    change P.edgeSet = T.interval.front.edgeSet
    exact LinkageBlueprint.liftOriginal_edgeSet T.interval.front
  have hPE : Q.edgeSet ⊆
      M.oldPriorityAttachedEdges A := by
    rw [hQedge]
    exact
      M.front_edgeSet_subset_oldPriorityAttachedEdges
        current A hcurrent hzTerminal hAE hAV
  have hzCurrent : z ∈ current.vertexSet := by
    obtain ⟨p, hp, hpTerminal⟩ := hzTerminal
    exact ⟨p, hp,
      (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminal_mem_support
        hpTerminal⟩
  have hzCarrier : Q.initial ∈
      RootReachableRelation.carrier
        (M.oldPriorityAttachedEdges A) A.initialSet := by
    change P.start ∈ RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet
    change T.interval.front.start ∈ RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet
    rw [T.interval.front_start]
    rw [← hUV]
    exact hAU.1 (hcurrentA.1 hzCurrent)
  have hretained := RootReachableRelation.path_edgeSet_subset_edges
    (Gamma := imaginaryWeb Gamma C.ladder.limitWarp kappa)
    (M.oldPriorityAttachedEdges A) A.initialSet Q hPE hzCarrier
  rw [← hUE] at hretained
  rw [hQedge] at hretained
  exact hretained

/-- The root-reachable restriction retains every vertex of the safe front,
including its captured-frontier endpoint.  This is the carrier companion to
`front_edgeSet_subset_rootReachableBlueprint`; it also covers the degenerate
front, where there need not be an edge witnessing the endpoint. -/
theorem front_support_subset_rootReachableBlueprint
    (M : PostClosureMacroCompressorAssignment T)
    (current A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hzTerminal : z ∈ current.terminalSet)
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
    T.interval.front.support ⊆ U.vertexSet := by
  let P : FinitePath (imaginaryGraph Gamma C.ladder.limitWarp kappa) :=
    LinkageBlueprint.liftOriginal T.interval.front
  let Q : (imaginaryWeb Gamma C.ladder.limitWarp kappa).DPath := .inl P
  have hQsupport : Q.support = T.interval.front.support := by
    change P.support = T.interval.front.support
    exact LinkageBlueprint.liftOriginal_support T.interval.front
  have hQedge : Q.edgeSet = T.interval.front.edgeSet := by
    change P.edgeSet = T.interval.front.edgeSet
    exact LinkageBlueprint.liftOriginal_edgeSet T.interval.front
  have hPE : Q.edgeSet ⊆ M.oldPriorityAttachedEdges A := by
    rw [hQedge]
    exact M.front_edgeSet_subset_oldPriorityAttachedEdges
      current A hcurrent hzTerminal hAE hAV
  have hzCurrent : z ∈ current.vertexSet := by
    obtain ⟨p, hp, hpTerminal⟩ := hzTerminal
    exact ⟨p, hp,
      (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminal_mem_support
        hpTerminal⟩
  have hzCarrier : Q.initial ∈ RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet := by
    change T.interval.front.start ∈ RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet
    rw [T.interval.front_start, ← hUV]
    exact hAU.1 (hcurrentA.1 hzCurrent)
  have hretained := RootReachableRelation.path_support_subset_carrier
    (Gamma := imaginaryWeb Gamma C.ladder.limitWarp kappa)
    (M.oldPriorityAttachedEdges A) A.initialSet Q hPE hzCarrier
  rw [← hUV, hQsupport] at hretained
  exact hretained

#print axioms front_edgeSet_subset_oldPriorityFreshEdges
#print axioms front_edgeSet_subset_rootReachableBlueprint
#print axioms front_support_subset_rootReachableBlueprint

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
