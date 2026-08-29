/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.IndexedRelationLimitBoundary
import ErdosProblems.Erdos599.DeferredLimitHitClosure

/-!
# Moving-source retention from ladder hit closure

The global reference warp in the half-way construction is the limiting
ladder warp.  It may contain rays, so finite-support compactness is not an
appropriate canonical argument for moving source coverage.  Instead,
source Lemma 7.28 already supplies exactly the required continuity:
the hit stages of every limiting ladder component are closed under directed
suprema.

This module first exposes that pathwise fact for an arbitrary monotone
indexed family, including an attained supremum.  It then applies it directly
to `IndexedRealExtensionChain`: a source vertex outside the limit carrier
is represented by one reference component at every stage, hence that same
component meets the frontier at the indexed supremum.  No finite-character
hypothesis on the reference warp is used.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

universe u v

variable {V : Type u} {G : DWeb V} {kappa : Cardinal.{u}}
variable {L : G.KappaLadder kappa}
variable {I : Type v} [LinearOrder I] [Nonempty I]

/-- A limiting ladder component which meets every stage of a monotone
indexed family meets the frontier at the least upper bound.  The theorem
also covers the attained case. -/
theorem limitWarp_meets_frontier_at_iSup
    {Sigma : Set (Ladder.Stage kappa)}
    (hHit : LimitHitClosure G L Sigma)
    (stageIndex : I → Ladder.Stage kappa)
    (hmono : Monotone stageIndex)
    {a : Ladder.Stage kappa}
    (hLUB : IsLUB (Set.range stageIndex) a)
    (hSigma : ∀ i, stageIndex i ∈ Sigma)
    {p : G.DPath} (hp : p ∈ L.limitWarp)
    (hmeet : ∀ i,
      (p.support ∩ L.frontier (stageIndex i)).Nonempty) :
    (p.support ∩ L.frontier a).Nonempty := by
  let d : Set (Ladder.Stage kappa) := Set.range stageIndex
  have hd : d ⊆ L.hitStages Sigma p := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, hxp, hxFrontier⟩ := hmeet i
    exact ⟨hSigma i, x, hxFrontier, hxp⟩
  have hdne : d.Nonempty := by
    let i : I := Classical.choice inferInstance
    exact ⟨stageIndex i, i, rfl⟩
  have hddir : DirectedOn (· ≤ ·) d := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    refine ⟨stageIndex (max i j), ⟨max i j, rfl⟩, ?_, ?_⟩
    · exact hmono (le_max_left i j)
    · exact hmono (le_max_right i j)
  have haHit : a ∈ L.hitStages Sigma p :=
    hHit p hp hd hdne hddir hLUB
  obtain ⟨x, hxFrontier, hxp⟩ := haHit.2
  exact ⟨x, hxp, hxFrontier⟩

/-- Tail form: meeting every stage above one index is enough, because a
tail of a monotone family has the same least upper bound. -/
theorem limitWarp_meets_frontier_at_iSup_of_eventually
    {Sigma : Set (Ladder.Stage kappa)}
    (hHit : LimitHitClosure G L Sigma)
    (stageIndex : I → Ladder.Stage kappa)
    (hmono : Monotone stageIndex)
    {a : Ladder.Stage kappa}
    (hLUB : IsLUB (Set.range stageIndex) a)
    (hSigma : ∀ i, stageIndex i ∈ Sigma)
    {p : G.DPath} (hp : p ∈ L.limitWarp)
    (i₀ : I)
    (hmeet : ∀ j, i₀ ≤ j →
      (p.support ∩ L.frontier (stageIndex j)).Nonempty) :
    (p.support ∩ L.frontier a).Nonempty := by
  let Tail := Set.Ici i₀
  let tailIndex : Tail → Ladder.Stage kappa := fun i ↦ stageIndex i.1
  have htailMono : Monotone tailIndex := by
    intro i j hij
    exact hmono hij
  have htailLUB : IsLUB (Set.range tailIndex) a := by
    constructor
    · rintro _ ⟨i, rfl⟩
      exact hLUB.1 ⟨i.1, rfl⟩
    · intro b hb
      apply hLUB.2
      rintro _ ⟨i, rfl⟩
      rcases le_total i i₀ with hii₀ | hi₀i
      · exact (hmono hii₀).trans (hb ⟨⟨i₀, le_rfl⟩, rfl⟩)
      · exact hb ⟨⟨i, hi₀i⟩, rfl⟩
  exact limitWarp_meets_frontier_at_iSup hHit tailIndex htailMono
    htailLUB (fun i ↦ hSigma i.1) hp (fun i ↦ hmeet i.1 i.2)

end Deferred
end KappaLadder
end DWeb

namespace Blueprint
namespace LinkageBlueprint
namespace IndexedRealExtensionChain

universe u v

variable {V : Type u} {I : Type v} [LinearOrder I] [Nonempty I]
variable {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa theta : Cardinal.{u}}
variable {B : Set V}

/-- Moving source coverage for a reference warp contained in the global
limiting ladder warp.  Rays are allowed: frontier continuity is supplied
by `LimitHitClosure`, not by finite support. -/
theorem eventualRelationBlueprint_covers_source_of_limitHitClosure
    (C : IndexedRealExtensionChain I Gamma Y kappa B)
    (L : Gamma.KappaLadder theta)
    {Sigma : Set (Ladder.Stage theta)}
    (hHit : DWeb.KappaLadder.Deferred.LimitHitClosure Gamma L Sigma)
    (stageIndex : I → Ladder.Stage theta)
    (hmono : Monotone stageIndex)
    {a : Ladder.Stage theta}
    (hLUB : IsLUB (Set.range stageIndex) a)
    (hSigma : ∀ i, stageIndex i ∈ Sigma)
    (hcover : ∀ i, Gamma.source ⊆ (C.stage i).initialSet ∪
      (C.stage i).retainedReferenceInitials
        (L.frontier (stageIndex i)))
    (hYwarp : Gamma.IsWarp Y)
    (hYlimit : Y ⊆ L.limitWarp) :
    Gamma.source ⊆ C.eventualRelationBlueprint.initialSet ∪
      C.eventualRelationBlueprint.retainedReferenceInitials
        (L.frontier a) := by
  classical
  intro source hsource
  by_cases hsourceLimit : source ∈ C.realVertexLimit
  · apply Or.inl
    rw [eventualRelationBlueprint,
      orientationBlueprint_initialSet_eq_no_incoming,
      C.eventualRelationOrientation_spec.1,
      C.eventualRelationOrientation_spec.2]
    exact C.source_mem_eventualRelationRoots
      (fun i ↦ L.frontier (stageIndex i)) hcover hsource hsourceLimit
  · have hretained : ∀ i,
        source ∈ (C.stage i).retainedReferenceInitials
          (L.frontier (stageIndex i)) := by
      intro i
      rcases hcover i hsource with hinitial | hretained
      · rcases hinitial with ⟨p, hp, rfl⟩
        exact False.elim <| hsourceLimit <|
          C.stage_vertices_subset_realVertexLimit i
            ⟨p, hp, p.initial_mem_support⟩
      · exact hretained
    let i₀ : I := Classical.choice inferInstance
    obtain ⟨p, ⟨hpFrontier, hpNotStage⟩, hpInitial⟩ := hretained i₀
    have hpMeet : ∀ i,
        (p.support ∩ L.frontier (stageIndex i)).Nonempty := by
      intro i
      obtain ⟨q, ⟨hqFrontier, _hqNotStage⟩, hqInitial⟩ := hretained i
      have hqp : q = p := by
        by_contra hne
        exact Set.disjoint_left.1 (hYwarp hqFrontier.1 hpFrontier.1 hne)
          (hqInitial ▸ q.initial_mem_support)
          (hpInitial ▸ p.initial_mem_support)
      exact hqp ▸ hqFrontier.2
    have hpMeetLimit :
        (p.support ∩ L.frontier a).Nonempty :=
      DWeb.KappaLadder.Deferred.limitWarp_meets_frontier_at_iSup
        hHit stageIndex hmono hLUB hSigma (hYlimit hpFrontier.1) hpMeet
    have hpNotLimitCarrier :
        ¬ (p.support ∩ C.realVertexLimit).Nonempty := by
      rintro ⟨x, hxp, hxLimit⟩
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxLimit
      obtain ⟨q, ⟨hqFrontier, hqNotStage⟩, hqInitial⟩ := hretained i
      have hqp : q = p := by
        by_contra hne
        exact Set.disjoint_left.1 (hYwarp hqFrontier.1 hpFrontier.1 hne)
          (hqInitial ▸ q.initial_mem_support)
          (hpInitial ▸ p.initial_mem_support)
      subst q
      exact hqNotStage ⟨hpFrontier.1, x, hxp, hxi⟩
    apply Or.inr
    refine ⟨p, ⟨⟨hpFrontier.1, hpMeetLimit⟩, ?_⟩, hpInitial⟩
    intro hpMeetCarrier
    apply hpNotLimitCarrier
    simpa only [C.eventualRelationBlueprint_vertexSet] using
      hpMeetCarrier.2

end IndexedRealExtensionChain
end LinkageBlueprint
end Blueprint
end Erdos599
