/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGlobalLocalReferenceTransport
import ErdosProblems.Erdos599.HalfwaySourceRootPruning

/-!
# Finite local replacement for the global reference remainder

The global limiting ladder warp can contain rays, so retaining its whole
members after they hit the selected frontier does not give endpoint purity.
Instead we retain the finite selected-stage reference prefixes with original
source initials and disjoint support.  Global-to-local prefix transport shows
that this family preserves every source initial required by blueprint
condition (2).
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa rho : Cardinal.{u}}

/-- The source-starting, carrier-disjoint part of the finite reference at a
selected ladder stage. -/
def localizedReferenceRemainder
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho) :
    Set Gamma.DPath :=
  {p | p ∈ ladderReference L a ∧ p.initial ∈ Gamma.source ∧
    Disjoint p.support U.vertexSet}

theorem localizedReferenceRemainder_subset
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho) :
    localizedReferenceRemainder L a U ⊆ ladderReference L a :=
  fun _ hp ↦ hp.1

theorem localizedReferenceRemainder_isWarp
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Gamma.IsWarp (localizedReferenceRemainder L a U) := by
  intro p hp q hq hpq
  exact ladderReference.isWarp hL hp.1 hq.1 hpq

theorem localizedReferenceRemainder_finiteCharacter
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho) :
    Gamma.HasFiniteCharacter (localizedReferenceRemainder L a U) := by
  intro p hp
  exact ladderReference.finiteCharacter hp.1

theorem localizedReferenceRemainder_initialSet_subset_source
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho) :
    Gamma.initialSet (localizedReferenceRemainder L a U) ⊆
      Gamma.source := by
  rintro x ⟨p, hp, rfl⟩
  exact hp.2.1

theorem localizedReferenceRemainder_terminalFrontier_subset
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Gamma.terminalFrontier (localizedReferenceRemainder L a U) ⊆
      L.frontier a := by
  rintro x ⟨p, hp, hpterminal⟩
  rw [← ladderReference.terminalFrontier_eq hL]
  exact ⟨p, hp.1, hpterminal⟩

theorem localizedReferenceRemainder_endpointPure
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho)
    (hGamma : Gamma.IsNormalized)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    ∀ p ∈ localizedReferenceRemainder L a U,
      CardinalInduction.IsPathBetween Gamma Gamma.source
        (L.frontier a) p :=
  ladderReference.endpointPure_of_initials hGamma hL
    (localizedReferenceRemainder_subset L a U)
    (fun _ hp ↦ hp.2.1)

theorem localizedReferenceRemainder_disjoint
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho) :
    ∀ p ∈ U.paths, ∀ q ∈ localizedReferenceRemainder L a U,
      Disjoint p.support q.support := by
  intro p hp q hq
  apply Set.disjoint_left.2
  intro x hxp hxq
  exact Set.disjoint_left.1 hq.2.2 hxq ⟨p, hp, hxp⟩

/-- Every global retained-reference initial required by blueprint condition
(2) is represented by a finite, source-starting local prefix. -/
theorem source_subset_initial_union_localizedReferenceRemainder
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Z persistent : Set V}
    (hU : U.IsLinkageBlueprint (L.frontier a) Z persistent) :
    Gamma.source ⊆ U.initialSet ∪
      Gamma.initialSet (localizedReferenceRemainder L a U) := by
  intro x hxSource
  rcases hU.covers_source hxSource with hxInitial | hxRetained
  · exact Or.inl hxInitial
  · right
    change x ∈ Gamma.initialSet (U.referenceRemainder (L.frontier a)) at hxRetained
    obtain ⟨p, hp, hpinitial⟩ := hxRetained
    obtain ⟨z, hzp, hzFrontier⟩ := hp.1.2
    obtain ⟨q, hqReference, _hqterminal, hqp⟩ :=
      ladderReference.exists_prefix_of_limitWarp_frontier_hit hL hp.1.1
        hzFrontier hzp
    have hqSource : q.initial ∈ Gamma.source := by
      rw [Gamma.extends_initial hqp, hpinitial]
      exact hxSource
    have hqDisjoint : Disjoint q.support U.vertexSet := by
      apply Set.disjoint_left.2
      intro y hyq hyU
      apply hp.2
      exact ⟨hp.1.1,
        ⟨y, Gamma.support_mono_of_extends hqp hyq, hyU⟩⟩
    refine ⟨q, ⟨hqReference, hqSource, hqDisjoint⟩, ?_⟩
    exact (Gamma.extends_initial hqp).trans hpinitial

/-- For a source-rooted blueprint the preceding source cover is exact. -/
theorem sourceRootBlueprint_initial_union_localizedReferenceRemainder
    (L : Gamma.KappaLadder kappa) (a : Ladder.Stage kappa)
    (U : LinkageBlueprint Gamma L.limitWarp rho)
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Z persistent : Set V}
    (hU : U.IsLinkageBlueprint (L.frontier a) Z persistent) :
    (sourceRootBlueprint U).initialSet ∪
      Gamma.initialSet
        (localizedReferenceRemainder L a (sourceRootBlueprint U)) =
      Gamma.source := by
  apply Set.Subset.antisymm
  · exact Set.union_subset
      (sourceRootBlueprint_initialSet_subset_source U)
      (localizedReferenceRemainder_initialSet_subset_source
        L a (sourceRootBlueprint U))
  · exact source_subset_initial_union_localizedReferenceRemainder
      L a (sourceRootBlueprint U) hL
      (sourceRootBlueprint_isLinkageBlueprint U hU)

end LinkageBlueprint
end Blueprint
end Erdos599
