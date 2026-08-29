/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualReservedParent
import ErdosProblems.Erdos599.SplitGroundingGroundedEqualSelection

/-!
# Concrete stationary equal selection for split grounding

This bundles the complete unconditional output of the collision-recursive
selection in the split equal branch: a genuinely grounded reserved route,
its original source-rooted inessential parent, and a stationary target-pure
family whose decoded carriers are pairwise disjoint and avoid that parent's
collision carrier.
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

/-- All source-faithful data obtained unconditionally from a stationary
grounded equal-index target family. -/
structure SplitReservedStationaryEqualSelection
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target) where
  reserved : FinitePath (L.splitPopularAuxiliaryInput hL.legal).lambda.graph
  reserved_mem : reserved ∈
    ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
  reserved_source : reserved.start ∈
    (L.splitPopularAuxiliaryInput hL.legal).lambda.source
  reserved_ground : (L.splitPopularAuxiliaryIndexed hL).f
    ⟨reserved.start, reserved_source⟩ ∈ L.phiGround
  parent : L.SplitReservedGroundedParent hL reserved reserved_source
  routes : Popular.XSWarp
    (L.splitPopularAuxiliaryInput hL.legal).lambda
    (L.splitPopularAuxiliaryInput hL.legal).lambda.target
  routes_subset : routes.paths ⊆
    ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
  routes_targetPure : ∀ p ∈ routes.paths,
    (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p
  routes_ground : ∀ p, ∀ hp : p ∈ routes.paths,
    (L.splitPopularAuxiliaryIndexed hL).f
      ⟨p.start, routes.starts_in_source hp⟩ ∈ L.phiGround
  equal_indices_stationary : Stationary.IsStationaryBelow kappa
    (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp routes).paths
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp routes).starts_in_source)
  decodedCarriers_pairwiseDisjoint : routes.paths.PairwiseDisjoint
    (L.splitPopularAuxiliaryInput hL.legal).decodedVertexCarrier
  routes_avoid_reserved : ∀ p ∈ routes.paths,
    Disjoint p.support
      (collisionCarrier (L.splitPopularAuxiliaryInput hL.legal) reserved)
  routes_orderedAvoidance : ∀ {p q}
      (hp : p ∈ routes.paths) (hq : q ∈ routes.paths),
    (L.splitPopularAuxiliaryIndexed hL).f
        ⟨q.start, routes.starts_in_source hq⟩ <
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.start, routes.starts_in_source hp⟩ →
    Disjoint p.support
      (collisionCarrier (L.splitPopularAuxiliaryInput hL.legal) q)

/-- The strengthened selection recursion and grounded-parent decoder provide
the bundled split equal selection without any provider hypothesis. -/
theorem splitReservedStationaryEqualSelection_nonempty
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (P : Popular.XSWarp
      (L.splitPopularAuxiliaryInput hL.legal).lambda
      (L.splitPopularAuxiliaryInput hL.legal).lambda.target)
    (hpure : ∀ p ∈ P.paths,
      (L.splitPopularAuxiliaryInput hL.legal).IsTargetPure p)
    (hstat : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf (L.splitPopularAuxiliaryIndexed hL)
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source ∩
        L.phiGround)) :
    Nonempty (L.SplitReservedStationaryEqualSelection hL P) := by
  obtain ⟨q, hq, hqground, Q, hQP, hQpure, hQground,
      hQstat, hQdisjoint, hQavoid, hQordered⟩ :=
    L.exists_splitReserved_grounded_targetPure_stationary_equalSubwarp
      hL P hpure hstat
  let hs : q.start ∈
      (L.splitPopularAuxiliaryInput hL.legal).lambda.source :=
    ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source hq
  let R : L.SplitReservedGroundedParent hL q hs :=
    (L.splitReservedGroundedParent_nonempty hL q hs hqground).some
  exact ⟨{
    reserved := q
    reserved_mem := hq
    reserved_source := hs
    reserved_ground := hqground
    parent := R
    routes := Q
    routes_subset := hQP
    routes_targetPure := hQpure
    routes_ground := hQground
    equal_indices_stationary := hQstat
    decodedCarriers_pairwiseDisjoint := hQdisjoint
    routes_avoid_reserved := hQavoid
    routes_orderedAvoidance := hQordered }⟩

namespace SplitReservedStationaryEqualSelection

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {P : Popular.XSWarp
    (L.splitPopularAuxiliaryInput hL.legal).lambda
    (L.splitPopularAuxiliaryInput hL.legal).lambda.target}

/-- The selected routes' decoded carriers avoid the reserved original
parent. -/
theorem routes_disjoint_parent
    (S : L.SplitReservedStationaryEqualSelection hL P) :
    ∀ p ∈ S.routes.paths,
      Disjoint
        ((L.splitPopularAuxiliaryInput hL.legal).decodedVertexCarrier p)
        S.parent.parent.support :=
  S.parent.decodedCarriers_disjoint S.routes S.routes_avoid_reserved

/-- The reserved original source cannot reach the essential terminal cut in
the selected collision-repaired relation. -/
theorem reservedSource_not_reaches_terminalCut
    (S : L.SplitReservedStationaryEqualSelection hL P)
    {b : V}
    (hb : b ∈ (L.splitPopularAuxiliaryInput hL.legal).terminalCut) :
    ¬ Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
        (L.splitPopularAuxiliaryInput hL.legal) S.routes)
      S.parent.parent.initial b :=
  S.parent.not_reaches_terminalCut S.routes
    S.routes_avoid_reserved hb

end SplitReservedStationaryEqualSelection
end KappaLadder
end DWeb
end Erdos599


