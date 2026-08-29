/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualCompiler
import ErdosProblems.Erdos599.GroundingEqualDecodedMaximalWarp

/-!
# Maximal collision-safe supply for the split equal branch

The stationary collision-disjoint family extends by Zorn to a target-pure
maximal family which still avoids the reserved route and remains disjoint in
decoded original carriers.  This is the coverage reservoir used by the
active route transaction.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open GroundingEqualActiveSelection
open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Auxiliary source vertices whose chronological index belongs to the
grounded stationary set. -/
def splitGroundedAuxiliarySources
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    Set (L.splitPopularAuxiliaryInput hL.legal).LV :=
  {x | ∃ hx : x ∈ (L.splitPopularAuxiliaryInput hL.legal).lambda.source,
    (L.splitPopularAuxiliaryIndexed hL).f ⟨x, hx⟩ ∈ L.phiGround}

/-- Grounded auxiliary sources are genuine sources of the split auxiliary. -/
theorem splitGroundedAuxiliarySources_subset_source
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :
    L.splitGroundedAuxiliarySources hL ⊆
      (L.splitPopularAuxiliaryInput hL.legal).lambda.source := by
  rintro x ⟨hx, _⟩
  exact hx

namespace SplitReservedStationaryEqualSelection

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {P : Popular.XSWarp
    (L.splitPopularAuxiliaryInput hL.legal).lambda
    (L.splitPopularAuxiliaryInput hL.legal).lambda.target}

/-- The selected stationary routes extend to a maximal target-pure,
decoded-carrier-disjoint family excluding the reserved auxiliary source and
avoiding its complete collision carrier. -/
theorem exists_maximalDecodedTargetPureAvoidingSupply
    (S : L.SplitReservedStationaryEqualSelection hL P) :
    ∃ M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
        (L.splitPopularAuxiliaryInput hL.legal)
        (L.splitGroundedAuxiliarySources hL \ {S.reserved.start})
        (collisionCarrier
          (L.splitPopularAuxiliaryInput hL.legal) S.reserved),
      S.routes.paths ⊆ M.paths := by
  apply S.routes.exists_maximalDecodedTargetPureAvoidingRestricted_extension
  · exact S.decodedCarriers_pairwiseDisjoint
  · intro p hp
    refine ⟨?_, ?_⟩
    · exact ⟨S.routes.starts_in_source hp, S.routes_ground p hp⟩
    · intro heq
      exact Set.disjoint_left.1 (S.routes_avoid_reserved p hp)
        p.start_mem_support
        (heq ▸ (Or.inl (Or.inl S.reserved.start_mem_support)))
  · exact fun {_} hp ↦ S.routes_targetPure _ hp
  · exact fun {_} hp ↦ S.routes_avoid_reserved _ hp

end SplitReservedStationaryEqualSelection

/-- Forget a maximal split supply down to its source--target warp. -/
def splitMaximalEqualWarp
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {q : FinitePath (L.splitPopularAuxiliaryInput hL.legal).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (L.splitPopularAuxiliaryInput hL.legal)
      (L.splitGroundedAuxiliarySources hL \ {q.start})
      (collisionCarrier (L.splitPopularAuxiliaryInput hL.legal) q)) :
    Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target :=
  M.toXSWarp fun _ hx ↦
    L.splitGroundedAuxiliarySources_subset_source hL hx.1

@[simp] theorem splitMaximalEqualWarp_paths
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {q : FinitePath (L.splitPopularAuxiliaryInput hL.legal).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (L.splitPopularAuxiliaryInput hL.legal)
      (L.splitGroundedAuxiliarySources hL \ {q.start})
      (collisionCarrier (L.splitPopularAuxiliaryInput hL.legal) q)) :
    (splitMaximalEqualWarp (hL := hL) M).paths = M.paths := rfl

/-- The maximal split supply retains decoded-carrier disjointness. -/
theorem splitMaximalEqualWarp_decodedCarriers_pairwiseDisjoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {q : FinitePath (L.splitPopularAuxiliaryInput hL.legal).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (L.splitPopularAuxiliaryInput hL.legal)
      (L.splitGroundedAuxiliarySources hL \ {q.start})
      (collisionCarrier (L.splitPopularAuxiliaryInput hL.legal) q)) :
    (splitMaximalEqualWarp (hL := hL) M).paths.PairwiseDisjoint
      (L.splitPopularAuxiliaryInput hL.legal).decodedVertexCarrier :=
  M.decoded_disjoint

/-- Every route added by maximality still has a grounded auxiliary
source index. -/
theorem splitMaximalEqualWarp_routes_ground
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {q : FinitePath (L.splitPopularAuxiliaryInput hL.legal).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (L.splitPopularAuxiliaryInput hL.legal)
      (L.splitGroundedAuxiliarySources hL \ {q.start})
      (collisionCarrier (L.splitPopularAuxiliaryInput hL.legal) q)) :
    ∀ p, ∀ hp : p ∈ (splitMaximalEqualWarp (hL := hL) M).paths,
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.start,
          (splitMaximalEqualWarp (hL := hL) M).starts_in_source hp⟩ ∈
        L.phiGround := by
  intro p hp
  obtain ⟨hpSource, hpGround⟩ := (M.starts_in_allowed hp).1
  have hs :
      (⟨p.start,
          (splitMaximalEqualWarp (hL := hL) M).starts_in_source hp⟩ :
        (L.splitPopularAuxiliaryInput hL.legal).lambda.source) =
      ⟨p.start, hpSource⟩ := Subtype.ext rfl
  exact (congrArg (L.splitPopularAuxiliaryIndexed hL).f hs) ▸ hpGround

/-- Every maximal route still avoids the reserved collision carrier. -/
theorem splitMaximalEqualWarp_avoids_reserved
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {q : FinitePath (L.splitPopularAuxiliaryInput hL.legal).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (L.splitPopularAuxiliaryInput hL.legal)
      (L.splitGroundedAuxiliarySources hL \ {q.start})
      (collisionCarrier (L.splitPopularAuxiliaryInput hL.legal) q)) :
    ∀ p : FinitePath (L.splitPopularAuxiliaryInput hL.legal).lambda.graph,
      p ∈ (splitMaximalEqualWarp (hL := hL) M).paths →
      Disjoint p.support
        (collisionCarrier (L.splitPopularAuxiliaryInput hL.legal) q) :=
  fun _ hp ↦ M.paths_avoid hp

end KappaLadder
end DWeb
end Erdos599

