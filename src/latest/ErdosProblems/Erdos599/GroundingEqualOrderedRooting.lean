/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualRootPrefixSurvival
import ErdosProblems.Erdos599.SimultaneousAssignment

/-!
# Rooting an equal route before its own ordered switch

The ordered equal-stage selection makes every selected route other than
`q` avoid the grounded limiting-ladder component from which `q` starts.
Consequently the complete finite source prefix of `q` survives the
canonical repaired relation formed from precisely the routes of smaller
source index.  This file packages that fact in the source-reachability form
needed by an ordered, one-route-at-a-time switch.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection

variable {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
variable {P : Popular.XSWarp
  (L.popularAuxiliaryInput hL.legal).lambda
  (L.popularAuxiliaryInput hL.legal).lambda.target}

namespace OrderedReservedStationaryDiagonalEqualSelection

/-- The subwarp of routes strictly before an index is genuinely a subwarp
of the final ordered family. -/
theorem routesBeforeIndex_paths_subset_routes
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa) :
    (routesBeforeIndex S a).paths ⊆ S.routes.paths := by
  rintro p ⟨hp, _⟩
  exact hp

/-- Decoded-carrier disjointness is inherited by every strict initial
segment of the ordered route family. -/
theorem routesBeforeIndex_decodedDisjoint
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa) :
    (routesBeforeIndex S a).paths.PairwiseDisjoint
      (L.popularAuxiliaryInput hL.legal).decodedVertexCarrier := by
  intro p hp q hq hpq
  exact S.routes_decodedDisjoint
    (S.routesBeforeIndex_paths_subset_routes a hp)
    (S.routesBeforeIndex_paths_subset_routes a hq) hpq

/-- The canonical repaired relation of an ordered initial segment is
biunique. -/
theorem routesBeforeIndex_repairedEdges_biUnique
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈
      canonicalErasedRepairedEdges
        (L.popularAuxiliaryInput hL.legal) (routesBeforeIndex S a)) := by
  exact canonicalErasedRepairedEdges_biUnique
    (L.popularAuxiliaryInput hL.legal) (routesBeforeIndex S a)
      (S.routesBeforeIndex_decodedDisjoint a)

/-- The canonical repaired relation of an ordered initial segment consists
of edges of the original web. -/
theorem routesBeforeIndex_repairedEdges_subset_adj
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa) :
    canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal) (routesBeforeIndex S a) ⊆
        {e | Gamma.graph.Adj e.1 e.2} := by
  exact canonicalErasedRepairedEdges_subset_adj
    (L.popularAuxiliaryInput hL.legal) (routesBeforeIndex S a)

/-- Every earlier selected carrier avoids a limiting-ladder component used
by a backward link of `q`.  A contact would expose that component to the
earlier route, while ordered avoidance would then make `q` disjoint from a
component that its backward link actually traverses. -/
theorem earlierRoute_decodedCarrier_disjoint_backwardOwner
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (r q : WarpPath S.routes)
    (hrq : warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes r <
      warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩).links)
    (_hldir : l.direction = .backward)
    (parent : Gamma.DPath)
    (hparent : parent ∈ (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (hsub : l.path.IsSubpathOf parent) :
    Disjoint
      ((L.popularAuxiliaryInput hL.legal).decodedVertexCarrier r.1)
      parent.support := by
  let J := L.popularAuxiliaryInput hL.legal
  let Q := (L.popularAuxiliaryIndexed hL).equalSubwarp S.base
  let qQ : WarpPath Q := ⟨q.1, S.routes_subset_equalBase q.2⟩
  rw [Set.disjoint_left]
  intro x hxr hxparent
  have hparentExposed : parent ∈
      GroundingSimultaneousDecode.exposedLadderPaths J r.1 := by
    apply J.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
      (L.popularAuxiliary_proxyPathsFaithful hL) r.1
      (S.routes.starts_in_source r.2) hparent hxr hxparent
  have havoid := S.routes_later_decodedCarrier_disjoint_earlier_exposedParent
    q.2 r.2 hrq hparentExposed
  let y := l.path.start
  have hyq : y ∈ J.decodedVertexCarrier q.1 := by
    apply canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J Q qQ
    apply AltPath.link_support_subset_vertexSet hl
    exact l.path.start_mem_support
  have hyparent : y ∈ parent.support :=
    hsub.1 l.path.start_mem_support
  exact Set.disjoint_left.1 havoid hyq hyparent

/-- A finite prefix of an avoided limiting-ladder parent survives the
canonical repaired relation of an ordered initial segment. -/
theorem finiteParentPrefix_edgeSet_subset_repaired_beforeIndex
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (a : Stationary.Below kappa)
    (parent : Gamma.DPath)
    (hparent : parent ∈ (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (r : FinitePath Gamma.graph) (hr : r.edgeSet ⊆ parent.edgeSet)
    (havoid : ∀ q : WarpPath (routesBeforeIndex S a),
      Disjoint
        ((L.popularAuxiliaryInput hL.legal).decodedVertexCarrier q.1)
        parent.support) :
    r.edgeSet ⊆ canonicalErasedRepairedEdges
      (L.popularAuxiliaryInput hL.legal) (routesBeforeIndex S a) := by
  let J := L.popularAuxiliaryInput hL.legal
  let W := routesBeforeIndex S a
  intro e he
  have heParent : e ∈ parent.edgeSet := hr he
  have heFamily : e ∈ J.familyEdges := ⟨parent, hparent, heParent⟩
  by_cases heRepaired : e ∈ canonicalErasedRepairedEdges J W
  · exact heRepaired
  · exfalso
    by_cases heBackward : e ∈ canonicalErasedBackwardEdges J W
    · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackward
      obtain ⟨q, hqe⟩ := heBackward
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute J W q) hqe
      have hcarrier :=
        canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J W q
      exact Set.disjoint_left.1 (havoid q) (hcarrier hends.1)
        (parent.edgeSet_subset_support_prod heParent).1
    · have heResidual : e ∈ canonicalErasedResidualEdges J W :=
        ⟨heFamily, heBackward⟩
      have heConflict : e ∈ canonicalErasedForwardConflictEdges J W := by
        by_contra heNotConflict
        apply heRepaired
        exact Or.inl ⟨heResidual, heNotConflict⟩
      obtain ⟨f, hfForward, htail | hhead⟩ := heConflict
      · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
        obtain ⟨q, hqf⟩ := hfForward
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J W q) hqf
        have hcarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J W q
        exact Set.disjoint_left.1 (havoid q)
          (htail.symm ▸ hcarrier hends.1)
          (parent.edgeSet_subset_support_prod heParent).1
      · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
        obtain ⟨q, hqf⟩ := hfForward
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J W q) hqf
        have hcarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J W q
        exact Set.disjoint_left.1 (havoid q)
          (hhead.symm ▸ hcarrier hends.2)
          (parent.edgeSet_subset_support_prod heParent).2

/-- Every grounded limiting-ladder owner of a backward link of `q` has its
ambient link start source-rooted before `q` is switched. -/
theorem backwardOwner_start_sourceRooted_beforeIndex
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal)
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩).links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath)
    (hparent : parent ∈ (L.popularAuxiliaryInput hL.legal).ladder.paths)
    (hparentSource : parent.initial ∈ Gamma.source)
    (hsub : l.path.IsSubpathOf parent) :
    ∃ x ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ canonicalErasedRepairedEdges
          (L.popularAuxiliaryInput hL.legal)
          (routesBeforeIndex S
            (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)))
        x l.path.start := by
  let a := warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q
  obtain ⟨r, hrStart, hrFinish, _hrSupport, hrEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix parent
      (hsub.1 l.path.start_mem_support)
  have havoid : ∀ p : WarpPath (routesBeforeIndex S a),
      Disjoint
        ((L.popularAuxiliaryInput hL.legal).decodedVertexCarrier p.1)
        parent.support := by
    intro p
    obtain ⟨hpRoutes, hpIndex⟩ := p.2
    exact S.earlierRoute_decodedCarrier_disjoint_backwardOwner
      ⟨p.1, hpRoutes⟩ q hpIndex l hl hldir parent hparent hsub
  have hrSurvives := S.finiteParentPrefix_edgeSet_subset_repaired_beforeIndex
    a parent hparent r hrEdges havoid
  refine ⟨r.start, ?_, ?_⟩
  · simpa only [hrStart] using hparentSource
  · simpa only [hrFinish] using
      (GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
        r hrSurvives
        r.finish_mem_support)

/-- Immediately before `q` is switched, the initial vertex of its canonical
erased route is reachable from the original source. -/
theorem route_initial_sourceRooted_beforeIndex
    (S : L.OrderedReservedStationaryDiagonalEqualSelection hL P)
    (q : WarpPath S.routes)
    (R : L.CanonicalErasedRouteRootPrefix hL
      ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
      ⟨q.1, S.routes_subset_equalBase q.2⟩) :
    ∃ x ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ canonicalErasedRepairedEdges
          (L.popularAuxiliaryInput hL.legal)
          (routesBeforeIndex S
            (warpPathIndex (L.popularAuxiliaryIndexed hL) S.routes q)))
        x
        (canonicalErasedRoute
          (L.popularAuxiliaryInput hL.legal)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp S.base)
          ⟨q.1, S.routes_subset_equalBase q.2⟩).initial := by
  obtain ⟨C⟩ := S.exists_firstRootParentCollision q R
  have howner : C.owner = q := C.owner_eq_route
  apply R.reaches_initial
  simpa only [howner] using C.rootPrefix_edgeSet_subset_repaired_beforeOwner

end OrderedReservedStationaryDiagonalEqualSelection
end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.routesBeforeIndex_repairedEdges_biUnique
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.routesBeforeIndex_repairedEdges_subset_adj
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.earlierRoute_decodedCarrier_disjoint_backwardOwner
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.backwardOwner_start_sourceRooted_beforeIndex
#print axioms Erdos599.DWeb.KappaLadder.OrderedReservedStationaryDiagonalEqualSelection.route_initial_sourceRooted_beforeIndex
