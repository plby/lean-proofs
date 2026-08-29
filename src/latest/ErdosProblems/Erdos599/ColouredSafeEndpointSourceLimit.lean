/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointHistoryBoundary
import ErdosProblems.Erdos599.AugmentedAccountedChainExactLimit
import ErdosProblems.Erdos599.DeferredLegalLimitHitClosure
import ErdosProblems.Erdos599.IndexedRelationLimitHitSource

/-!
# Source coverage of the actual endpoint-graph limit

The unchanged full limiting reference covers every source not represented in
the exact union. Its owner is the same at every stage, and limit-hit closure
puts that owner on the supremum frontier even if it is a ray.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {I : Type v} [LinearOrder I] {index : I → Stage (succ kappa)}

/-- Exactly the source-cover field already present in endpoint blueprints. -/
def CoversSource (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (W : Set (web C).DPath) (T : Set V) : Prop :=
  Gamma.source ⊆ (web C).initialSet W ∪ Gamma.initialSet
    (referencePathsMeeting C.ladder.limitWarp T \
      referencePathsMeeting C.ladder.limitWarp ((web C).vertexSet W))

theorem source_mem_vertexUnion_of_reference_meets
    (R : AugmentedAccountedChain Gamma (web C) I)
    (hstage : ∀ i, IsBlueprint C (index i) (R.stage i))
    {p : Gamma.DPath} (hp : p ∈ C.ladder.limitWarp) (ha : p.initial ∈ Gamma.source)
    (hmeet : (p.support ∩ R.vertexUnion).Nonempty) : p.initial ∈ R.vertexUnion := by
  obtain ⟨x, hxp, hx⟩ := hmeet
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  rcases (hstage i).covers_source ha with hinitial | hreference
  · exact R.stage_vertices_subset i (initialSet_subset_vertexSet (R.stage i) hinitial)
  · obtain ⟨q, hq, hqp⟩ := hreference
    have heq : q = p := DWeb.IsWarp.eq_of_mem_support
      (C.legal.warpStages (finalStage (succ kappa))) hq.1.1 hp
      (hqp ▸ q.initial_mem_support) p.initial_mem_support
    subst q
    exact False.elim (hq.2 ⟨hp, x, hxp, hxi⟩)

theorem coversSource_of_exact_eventualWarp
    (R : AugmentedAccountedChain Gamma (web C) I)
    (hstage : ∀ i, IsBlueprint C (index i) (R.stage i))
    {U : Set (web C).DPath} (hU : (web C).IsWarp U)
    (hUV : (web C).vertexSet U = R.vertexUnion) (hUE : familyEdges U = R.eventualEdges)
    (i : I) : CoversSource C U (C.ladder.frontier (index i)) := by
  intro a ha
  by_cases haV : a ∈ R.vertexUnion
  · left
    rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp hU, hUV, hUE]
    exact ⟨haV, R.eventualEdges_source_no_incoming ha⟩
  · right
    rcases (hstage i).covers_source ha with hinitial | hreference
    · exact False.elim (haV (R.stage_vertices_subset i
        (initialSet_subset_vertexSet (R.stage i) hinitial)))
    · obtain ⟨p, hp, hpa⟩ := hreference
      refine ⟨p, ⟨hp.1, ?_⟩, hpa⟩
      rintro ⟨_hpY, x, hxp, hxU⟩
      have haUnion := source_mem_vertexUnion_of_reference_meets R hstage hp.1.1
        (hpa ▸ ha) ⟨x, hxp, hUV ▸ hxU⟩
      exact haV (hpa ▸ haUnion)

theorem coversSource_at_lub [Nonempty I]
    (index : I → Stage (succ kappa)) (hmono : Monotone index)
    {a : Stage (succ kappa)} (hLUB : IsLUB (Set.range index) a)
    (hclub : ∀ i, index i ∈ C.club)
    {U : Set (web C).DPath}
    (hcover : ∀ i, CoversSource C U (C.ladder.frontier (index i))) :
    CoversSource C U (C.ladder.frontier a) := by
  classical
  intro source hsource
  by_cases hroot : source ∈ (web C).initialSet U
  · exact Or.inl hroot
  · have hretained : ∀ i, source ∈ Gamma.initialSet
        (referencePathsMeeting C.ladder.limitWarp (C.ladder.frontier (index i)) \
          referencePathsMeeting C.ladder.limitWarp ((web C).vertexSet U)) :=
      fun i ↦ (hcover i hsource).resolve_left hroot
    let i0 : I := Classical.choice inferInstance
    obtain ⟨p, hp, hpa⟩ := hretained i0
    have hmeet : ∀ i, (p.support ∩ C.ladder.frontier (index i)).Nonempty := by
      intro i
      obtain ⟨q, hq, hqa⟩ := hretained i
      have hqp : q = p := DWeb.IsWarp.eq_of_mem_support
        (C.legal.warpStages (finalStage (succ kappa))) hq.1.1 hp.1.1
        (hqa ▸ q.initial_mem_support) (hpa ▸ p.initial_mem_support)
      exact hqp ▸ hq.1.2
    have hlimit := DWeb.KappaLadder.Deferred.limitWarp_meets_frontier_at_iSup
      C.limitHitClosure index hmono hLUB hclub hp.1.1 hmeet
    exact Or.inr ⟨p, ⟨⟨hp.1.1, hlimit⟩, hp.2⟩, hpa⟩

#print axioms source_mem_vertexUnion_of_reference_meets
#print axioms coversSource_of_exact_eventualWarp
#print axioms coversSource_at_lub

end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
