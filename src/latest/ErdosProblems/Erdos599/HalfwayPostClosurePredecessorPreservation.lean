/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureDeadEndBoundary

/-!
# Full predecessor preservation of the concrete post-closure attachment

Each of the three literal attachment steps preserves every incoming edge at
the preceding carrier:

* activated reference prefixes are disjoint from the current blueprint;
* fresh closed edges enter no vertex of the old-roof prefix seed;
* the final target tail meets the pre-tail carrier only at its start, and no
  tail edge enters that start.

Their composition gives the full predecessor invariant required by the
indexed moving successor, with no abstract incidence premise.
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

/-- Adding the disjoint activated reference-prefix family introduces no new
incoming edge at a current vertex. -/
theorem noNewPredecessors_referencePrefixSeed
    (current A : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hAE : A.edgeSet =
      referencePrefixSeedEdges current Rlimit.closedSet) :
    current.NoNewPredecessorsTo A := by
  intro x y hxCurrent hyx
  rw [hAE] at hyx
  rcases hyx with hyxOld | hyxPrefix
  · exact hyxOld
  · exfalso
    have hxPrefix := (familyEdges_subset_vertexSet_prod
      (activatedReferencePrefixes C current Rlimit.closedSet) hyxPrefix).2
    exact Set.disjoint_left.1 referencePrefixSeed.vertexSets_disjoint
      hxCurrent hxPrefix

/-- Root-reachable restriction of the old-priority relation introduces no
new incoming edge at a vertex of the prefixed seed. -/
theorem noNewPredecessors_rootReachableOldPriority
    (M : PostClosureMacroCompressorAssignment T)
    (A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (hAroof : A.vertexSet ⊆ Gamma.roof C.newSlice)
    (hUE : U.edgeSet = RootReachableRelation.edges
      (M.oldPriorityAttachedEdges A) A.initialSet) :
    A.NoNewPredecessorsTo U := by
  intro x y hxA hyx
  rw [hUE] at hyx
  rcases hyx.1 with hyxOld | hyxFresh
  · exact hyxOld
  · exact False.elim
      ((M.oldPriorityFreshEdge_head_not_mem_of_vertices_roofed A hAroof
        hyxFresh) hxA)

/-- Appending a path which meets the old carrier only at its start creates
no new incoming edge at an old vertex. -/
theorem noNewPredecessors_tailExtension
    (U Vout : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    (P : FinitePath Gamma.graph)
    (hE : Vout.edgeSet = U.edgeSet ∪ P.edgeSet)
    (hfresh : U.vertexSet ∩ P.support ⊆ {P.start}) :
    U.NoNewPredecessorsTo Vout := by
  intro x y hxU hyx
  rw [hE] at hyx
  rcases hyx with hyxOld | hyxTail
  · exact hyxOld
  · exfalso
    have hxTail : x ∈ P.support :=
      (P.edgeSet_subset_support_prod hyxTail).2
    have hxStart : x = P.start :=
      Set.mem_singleton_iff.1 (hfresh ⟨hxU, hxTail⟩)
    exact Alternating.FinitePath.no_incoming_edge_at_start P y
      (by simpa only [hxStart] using hyxTail)

/-- Full predecessor preservation through the activated prefixes, the
root-reachable closed splice, and the literal target-tail diamond. -/
theorem noNewPredecessors_targetTailOutput
    (M : PostClosureMacroCompressorAssignment T)
    (current A U Vout : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hAE : A.edgeSet =
      referencePrefixSeedEdges current Rlimit.closedSet)
    (hAV : A.vertexSet = current.vertexSet ∪ Gamma.vertexSet
      (activatedReferencePrefixes C current Rlimit.closedSet))
    (hUE : U.edgeSet = RootReachableRelation.edges
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hUV : U.vertexSet = RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet)
    (hVE : Vout.edgeSet = U.edgeSet ∪ T.interval.tail.edgeSet) :
    current.NoNewPredecessorsTo Vout := by
  have hAroof : A.vertexSet ⊆ Gamma.roof C.newSlice :=
    referencePrefixSeed.blueprint_vertices_roofed hcurrent hAV
  have hcurrentA : current.NoNewPredecessorsTo A :=
    noNewPredecessors_referencePrefixSeed current A hAE
  have hAU : A.NoNewPredecessorsTo U :=
    M.noNewPredecessors_rootReachableOldPriority A U hAroof hUE
  have hfresh : U.vertexSet ∩ T.interval.tail.support ⊆
      {T.interval.tail.start} := by
    exact M.rootReachableBlueprint_tail_inter_subset current A U
      hcurrent hAV hUV
  have hUVout : U.NoNewPredecessorsTo Vout :=
    noNewPredecessors_tailExtension U Vout T.interval.tail hVE hfresh
  have hcurrentAvertices : current.vertexSet ⊆ A.vertexSet := by
    intro x hx
    rw [hAV]
    exact Or.inl hx
  have hAUvertices : A.vertexSet ⊆ U.vertexSet := by
    rw [hUV]
    apply RootReachableRelation.family_vertices_retained
    · exact M.current_edgeSet_subset_oldPriorityAttachedEdges A
    · intro x hx
      exact RootReachableRelation.roots_subset_carrier
        (M.oldPriorityAttachedEdges A) A.initialSet hx
  intro x y hx hyx
  exact hcurrentA hx
    (hAU (hcurrentAvertices hx)
      (hUVout (hAUvertices (hcurrentAvertices hx)) hyx))

#print axioms noNewPredecessors_referencePrefixSeed
#print axioms noNewPredecessors_rootReachableOldPriority
#print axioms noNewPredecessors_tailExtension
#print axioms noNewPredecessors_targetTailOutput

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
