/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureSafeFrontRetention

/-!
# The scheduled safe front ends at a genuine new terminal

The old-priority post-closure relation retains the selected safe front.  Its
captured-frontier endpoint has no outgoing edge in the candidate relation:
the seed has no outgoing edge there, and any literal or compressed fresh
edge would lie on the same finite interval member after its finish.  Hence
the endpoint is a terminal of the root-reachable blueprint.

This is deliberately only the old-to-captured-frontier part of the selected
target path.  Attaching its ambient-target tail requires a separate freshness
statement against the current blueprint and the activated reference prefixes.
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

private theorem front_finish_noOutgoing_intervalFamily
    {y : V}
    (hxy : (T.interval.front.finish, y) ∈
      familyEdges T.interval.ambientInterval) : False := by
  simp only [familyEdges, Set.mem_iUnion] at hxy
  obtain ⟨q, hq, hxyq⟩ := hxy
  have hfrontSupport : T.interval.front.finish ∈ T.interval.front.support :=
    T.interval.front.finish_mem_support
  have hqSupport : T.interval.front.finish ∈ q.support :=
    (q.edgeSet_subset_support_prod hxyq).1
  have heq : (Sum.inl T.interval.front : Gamma.DPath) = q :=
    DWeb.IsWarp.eq_of_mem_support
      T.interval.ambientInterval_linkage.isWarp
      T.interval.front_mem_interval hq hfrontSupport hqSupport
  subst q
  exact FinitePath.no_outgoing_edge_at_finish T.interval.front y hxyq

/-- Neither an inside-row edge nor a classified shortcut leaves the finish
of the scheduled front.  For a shortcut, its occurrence provenance supplies
the following literal forward interval edge, which is impossible after the
finish of the unique interval member containing that vertex. -/
theorem front_finish_noOutgoing_closedEdges
    (M : PostClosureMacroCompressorAssignment T) :
    ¬ ∃ y, (T.interval.front.finish, y) ∈
      M.toPostClosureCompressorAssignment.actualPostClosureClosedEdges := by
  rintro ⟨y, hxy⟩
  rcases hxy with hinside | hshortcut
  · exact front_finish_noOutgoing_intervalFamily hinside.1
  · let A := M.toPostClosureCompressorAssignment
    rw [A.mem_actualPostClosureShortcutEdges_iff] at hshortcut
    obtain ⟨s, hshortcut⟩ := hshortcut
    obtain ⟨b, hforward⟩ :=
      A.actualSegmentation_shortcut_tail_hasOutgoing_forward s hshortcut
    have hrow := M.assigned_forwardEdge_mem_outsideFamily s hforward
    exact front_finish_noOutgoing_intervalFamily hrow.1

private theorem front_finish_noOutgoing_seed
    (current A : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hzTerminal : z ∈ current.terminalSet)
    (hAE : A.edgeSet =
      referencePrefixSeedEdges current Rlimit.closedSet)
    (hAV : A.vertexSet = current.vertexSet ∪ Gamma.vertexSet
      (activatedReferencePrefixes C current Rlimit.closedSet)) :
    ¬ ∃ y, (T.interval.front.finish, y) ∈ A.edgeSet := by
  rintro ⟨y, hxy⟩
  have hAroof : A.vertexSet ⊆ Gamma.roof C.newSlice :=
    referencePrefixSeed.blueprint_vertices_roofed hcurrent hAV
  by_cases hfinish : T.interval.front.finish = z
  · rw [hAE] at hxy
    rcases hxy with hcurrentEdge | hprefixEdge
    · exact current_terminal_noOutgoing current hzTerminal
        ⟨y, hfinish ▸ hcurrentEdge⟩
    · have hzCurrent : z ∈ current.vertexSet := by
        obtain ⟨p, hp, hpTerminal⟩ := hzTerminal
        exact ⟨p, hp,
          (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminal_mem_support
            hpTerminal⟩
      have hzPrefix : z ∈ Gamma.vertexSet
          (activatedReferencePrefixes C current Rlimit.closedSet) := by
        have hend := familyEdges_subset_vertexSet_prod
          (activatedReferencePrefixes C current Rlimit.closedSet) hprefixEdge
        exact hfinish ▸ hend.1
      exact Set.disjoint_left.1 referencePrefixSeed.vertexSets_disjoint
        hzCurrent hzPrefix
  · have hfinishNeStart :
        T.interval.front.finish ≠ T.interval.front.start := by
      rwa [T.interval.front_start]
    obtain ⟨w, hw⟩ :=
      FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        T.interval.front T.interval.front.finish_mem_support hfinishNeStart
    have hwRow : (w, T.interval.front.finish) ∈
        familyEdges T.interval.ambientInterval :=
      Set.mem_iUnion.2 ⟨.inl T.interval.front,
        Set.mem_iUnion.2 ⟨T.interval.front_mem_interval, hw⟩⟩
    have hnotRoof : T.interval.front.finish ∉ Gamma.roof C.newSlice :=
      T.intervalFamilyEdge_head_not_mem_currentRoof hwRow
    apply hnotRoof
    apply hAroof
    change (T.interval.front.finish, y) ∈ familyEdges
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) A.paths at hxy
    exact (familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) A.paths hxy).1

/-- The captured-frontier endpoint of the scheduled front has no outgoing
edge in the complete old-priority candidate. -/
theorem front_finish_noOutgoing_oldPriorityAttachedEdges
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
    ¬ ∃ y, (T.interval.front.finish, y) ∈
      M.oldPriorityAttachedEdges A := by
  rintro ⟨y, hxy⟩
  rcases hxy with hseed | hfresh
  · exact front_finish_noOutgoing_seed current A hcurrent hzTerminal hAE hAV
      ⟨y, hseed⟩
  · exact M.front_finish_noOutgoing_closedEdges ⟨y, hfresh.1⟩

/-- The retained scheduled front therefore ends at an actual terminal of
the root-reachable output. -/
theorem front_finish_mem_terminalSet_rootReachableBlueprint
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
    T.interval.front.finish ∈ U.terminalSet := by
  change T.interval.front.finish ∈
    (imaginaryWeb Gamma C.ladder.limitWarp kappa).terminalFrontier U.paths
  rw [isWarp_terminalFrontier_eq_noOutgoing U.isWarp]
  refine ⟨M.front_support_subset_rootReachableBlueprint
    current A U hcurrent hzTerminal hcurrentA hAU hAE hAV hUE hUV
      T.interval.front.finish_mem_support, ?_⟩
  rintro ⟨y, hxy⟩
  change (T.interval.front.finish, y) ∈ U.edgeSet at hxy
  rw [hUE] at hxy
  exact M.front_finish_noOutgoing_oldPriorityAttachedEdges
    current A hcurrent hzTerminal hAE hAV ⟨y, hxy.1⟩

#print axioms front_finish_noOutgoing_closedEdges
#print axioms front_finish_noOutgoing_oldPriorityAttachedEdges
#print axioms front_finish_mem_terminalSet_rootReachableBlueprint

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
