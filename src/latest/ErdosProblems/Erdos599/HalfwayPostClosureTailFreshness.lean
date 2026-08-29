/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureSafeFrontLink

/-!
# Freshness of the stored target tail after closed-edge compression

Every endpoint of an actual compressed shortcut still lies on the literal
ambient interval row: the shortcut head has an incoming forward row edge,
and its tail has an outgoing forward row edge.  Hence the complete
old-priority relation is carried by the prefix seed together with that row.
The row meets the stored target suffix only at the splice point, as does the
prefix seed.  Root-reachable restriction therefore leaves the target suffix
fresh for one final literal diamond.
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

/-- Both endpoints of every actual inside/shortcut edge lie on the literal
ambient interval family. -/
theorem actualPostClosureClosedEdges_endpoints_ambientInterval
    (M : PostClosureMacroCompressorAssignment T)
    {e : V × V}
    (he : e ∈ (M.toPostClosureCompressorAssignment
      |>.actualPostClosureClosedEdges)) :
    e.1 ∈ Gamma.vertexSet T.interval.ambientInterval ∧
      e.2 ∈ Gamma.vertexSet T.interval.ambientInterval := by
  rcases he with hinside | hshortcut
  · exact familyEdges_subset_vertexSet_prod
      T.interval.ambientInterval hinside.1
  · let A := M.toPostClosureCompressorAssignment
    rw [A.mem_actualPostClosureShortcutEdges_iff] at hshortcut
    obtain ⟨s, hshortcut⟩ := hshortcut
    obtain ⟨w, htail⟩ :=
      A.actualSegmentation_shortcut_tail_hasOutgoing_forward s hshortcut
    obtain ⟨q, hhead⟩ :=
      A.segmentation_shortcut_head_hasIncoming_forward s
        (A.actualClosedClassifiedContactSegmentation s)
        (A.actualClosedClassifiedContactSegmentation_contactSet_subset s)
        hshortcut
    have htailRow := M.assigned_forwardEdge_mem_outsideFamily s htail
    have hheadRow := M.assigned_forwardEdge_mem_outsideFamily s hhead
    exact ⟨(familyEdges_subset_vertexSet_prod
      T.interval.ambientInterval htailRow.1).1,
      (familyEdges_subset_vertexSet_prod
        T.interval.ambientInterval hheadRow.1).2⟩

/-- The complete old-priority candidate uses no vertices beyond the exact
prefix seed and the literal ambient interval row. -/
theorem oldPriorityAttachedEdges_endpoints_seed_union_interval
    (M : PostClosureMacroCompressorAssignment T)
    (A : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {e : V × V} (he : e ∈ M.oldPriorityAttachedEdges A) :
    e.1 ∈ A.vertexSet ∪ Gamma.vertexSet T.interval.ambientInterval ∧
      e.2 ∈ A.vertexSet ∪ Gamma.vertexSet T.interval.ambientInterval := by
  rcases he with hseed | hfresh
  · change e ∈ familyEdges
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) A.paths at hseed
    have hend := familyEdges_subset_vertexSet_prod
      (Γ := imaginaryWeb Gamma C.ladder.limitWarp kappa) A.paths hseed
    exact ⟨Or.inl hend.1, Or.inl hend.2⟩
  · have hend := M.actualPostClosureClosedEdges_endpoints_ambientInterval
      hfresh.1
    exact ⟨Or.inr hend.1, Or.inr hend.2⟩

/-- The carrier selected by root reachability has the same sharp carrier
bound. -/
theorem rootReachableCarrier_subset_seed_union_interval
    (M : PostClosureMacroCompressorAssignment T)
    (A : LinkageBlueprint Gamma C.ladder.limitWarp kappa) :
    RootReachableRelation.carrier (M.oldPriorityAttachedEdges A) A.initialSet
      ⊆ A.vertexSet ∪ Gamma.vertexSet T.interval.ambientInterval := by
  apply RootReachableRelation.carrier_subset
  · intro x hx
    left
    obtain ⟨p, hp, hpInitial⟩ := hx
    exact ⟨p, hp, hpInitial.symm ▸ p.initial_mem_support⟩
  · exact fun e he ↦
      M.oldPriorityAttachedEdges_endpoints_seed_union_interval A he

/-- The actual root-reachable post-closure blueprint meets the stored target
suffix only at its splice vertex. -/
theorem rootReachableBlueprint_tail_inter_subset
    (M : PostClosureMacroCompressorAssignment T)
    (current A U : LinkageBlueprint Gamma C.ladder.limitWarp kappa)
    {currentClosed : Set V}
    (hcurrent : current.IsLinkageBlueprint
      C.newSlice currentClosed C.persistent)
    (hAV : A.vertexSet = current.vertexSet ∪ Gamma.vertexSet
      (activatedReferencePrefixes C current Rlimit.closedSet))
    (hUV : U.vertexSet = RootReachableRelation.carrier
      (M.oldPriorityAttachedEdges A) A.initialSet) :
    U.vertexSet ∩ T.interval.tail.support ⊆
      {T.interval.tail.start} := by
  intro x hx
  have hxCarrier : x ∈
      A.vertexSet ∪ Gamma.vertexSet T.interval.ambientInterval := by
    apply M.rootReachableCarrier_subset_seed_union_interval A
    rw [← hUV]
    exact hx.1
  rcases hxCarrier with hxA | hxInterval
  · exact referencePrefixSeed_tail_inter_subset
      (T := T) current A hcurrent hAV ⟨hxA, hx.2⟩
  · have hxContact : x ∈
        Gamma.vertexSet T.interval.ambientInterval ∩
          T.interval.tail.support := ⟨hxInterval, hx.2⟩
    rw [T.interval.interval_tail_inter] at hxContact
    simpa only [← T.interval.tail_start] using hxContact

#print axioms actualPostClosureClosedEdges_endpoints_ambientInterval
#print axioms oldPriorityAttachedEdges_endpoints_seed_union_interval
#print axioms rootReachableCarrier_subset_seed_union_interval
#print axioms rootReachableBlueprint_tail_inter_subset

end Erdos599.Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
