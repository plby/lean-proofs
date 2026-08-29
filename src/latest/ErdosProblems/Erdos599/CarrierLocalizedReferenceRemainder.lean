/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGlobalLocalReferenceTransport
import ErdosProblems.Erdos599.DeferredLadderRoofTransport
import ErdosProblems.Erdos599.SingularLinkageGeometry

/-!
# Finite reference remainder for an ordinary carrier

This is the carrier-parametric form of the localized reference construction.
Its paths and its prefix transport are in the original graph. No imaginary
graph or blueprint representation is part of the interface.
-/

namespace Erdos599.Blueprint.LinkageBlueprint

open Set Cardinal Order DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {theta : Cardinal.{u}}
variable (L : Gamma.KappaLadder theta) (a : Stage theta) (X : Set V)

def carrierReferenceRemainder : Set Gamma.DPath :=
  {p | p ∈ ladderReference L a ∧ p.initial ∈ Gamma.source ∧ Disjoint p.support X}

namespace carrierReferenceRemainder

theorem subset : carrierReferenceRemainder L a X ⊆ ladderReference L a := fun _ hp ↦ hp.1

theorem isWarp (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Gamma.IsWarp (carrierReferenceRemainder L a X) :=
  fun _ hp _ hq hpq ↦ ladderReference.isWarp hL hp.1 hq.1 hpq

theorem finiteCharacter : Gamma.HasFiniteCharacter (carrierReferenceRemainder L a X) := by
  intro p hp
  exact ladderReference.finiteCharacter hp.1

theorem initialSet_subset_source :
    Gamma.initialSet (carrierReferenceRemainder L a X) ⊆ Gamma.source := by
  rintro x ⟨p, hp, rfl⟩
  exact hp.2.1

theorem terminalFrontier_subset (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Gamma.terminalFrontier (carrierReferenceRemainder L a X) ⊆ L.frontier a := by
  rintro x ⟨p, hp, hpx⟩
  rw [← ladderReference.terminalFrontier_eq hL]
  exact ⟨p, hp.1, hpx⟩

theorem endpointPure (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    (hGamma : Gamma.IsNormalized) :
    ∀ p ∈ carrierReferenceRemainder L a X,
      CardinalInduction.IsPathBetween Gamma Gamma.source (L.frontier a) p :=
  ladderReference.endpointPure_of_initials hGamma hL (subset L a X) (fun _ hp ↦ hp.2.1)

theorem terminalClean (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    CardinalInduction.SingularContinuation.TerminalCleanAt Gamma
      (carrierReferenceRemainder L a X) (L.frontier a) := by
  intro p hp x hxp hx
  obtain ⟨q, rfl⟩ := finiteCharacter L a X hp
  have hxT : x ∈ Gamma.terminalFrontier (ladderReference L a) := by
    rwa [ladderReference.terminalFrontier_eq hL]
  have hxf : x = q.finish := Set.mem_singleton_iff.mp
    (DWeb.IsWarp.finite_support_inter_terminalFrontier Gamma
      (ladderReference.isWarp hL) hp.1 ⟨hxp, hxT⟩)
  subst x
  exact Gamma.terminal?_finite q

theorem vertexSet_subset_roof (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L) :
    Gamma.vertexSet (carrierReferenceRemainder L a X) ⊆ Gamma.roof (L.frontier a) := by
  apply Set.Subset.trans (b := Gamma.vertexSet (ladderReference L a))
  · rintro x ⟨p, hp, hxp⟩
    exact ⟨p, hp.1, hxp⟩
  · exact ladderReference.vertexSet_subset_roof hL
      (DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier hL a)

/-- A global source owner which meets the frontier gives a disjoint finite
local prefix with the same source. No finite-character claim about the
global limiting reference is needed. -/
theorem initialSet_cover (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {P : Set Gamma.DPath}
    (hPsource : Gamma.initialSet P ⊆ Gamma.source)
    (hcover : Gamma.source ⊆ Gamma.initialSet P ∪ Gamma.initialSet
      (referencePathsMeeting L.limitWarp (L.frontier a) \ referencePathsMeeting L.limitWarp X)) :
    Gamma.initialSet P ∪ Gamma.initialSet (carrierReferenceRemainder L a X) = Gamma.source := by
  apply Set.Subset.antisymm
  · exact Set.union_subset hPsource (initialSet_subset_source L a X)
  · intro x hx
    rcases hcover hx with hxP | ⟨p, hp, hpx⟩
    · exact Or.inl hxP
    · right
      obtain ⟨z, hzp, hzT⟩ := hp.1.2
      obtain ⟨q, hq, _hqT, hqp⟩ :=
        ladderReference.exists_prefix_of_limitWarp_frontier_hit hL hp.1.1 hzT hzp
      have hqx : q.initial = x := (Gamma.extends_initial hqp).trans hpx
      refine ⟨q, ⟨hq, hqx.symm ▸ hx, ?_⟩, hqx⟩
      apply Set.disjoint_left.mpr
      intro y hyq hyX
      exact hp.2 ⟨hp.1.1, y, Gamma.support_mono_of_extends hqp hyq, hyX⟩

theorem disjoint_family {P : Set Gamma.DPath} (hPX : Gamma.vertexSet P ⊆ X) :
    ∀ p ∈ P, ∀ q ∈ carrierReferenceRemainder L a X, Disjoint p.support q.support := by
  intro p hp q hq
  apply Set.disjoint_left.mpr
  intro x hxp hxq
  exact Set.disjoint_left.mp hq.2.2 hxq (hPX ⟨p, hp, hxp⟩)

#print axioms initialSet_cover
#print axioms terminalClean
#print axioms vertexSet_subset_roof

end carrierReferenceRemainder
end Erdos599.Blueprint.LinkageBlueprint
