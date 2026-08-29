/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalOrderedRootPrefix
import ErdosProblems.Erdos599.GroundingEqualOrderedTargetContact

/-!
# One-route switch in the maximal ordered active closure

For one active route, start with the canonical repaired relation of all
lower-index active routes.  Delete every old edge sharing a tail or head
with a current forward edge, then insert the current forward edges.  The
result is adjacent and locally bi-unique.  The canonical source root either
survives this transaction or the first deleted step is returned together
with the current forward edge responsible for the conflict.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingEqualMaximalCollisionForest
open GroundingEqualOrderedActiveSelection

variable {kappa : Cardinal.{u}}

private abbrev MaximalWarp
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :=
  ReservedMaximalDecodedActiveSupply.toXSWarp M

private abbrev ActiveWarp
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :=
  maximalOrderedActiveSubwarp hL M

/-- Earlier-relation edges conflicting in head or tail with the current
active route's forward relation. -/
def maximalActiveRouteForwardConflictEdges
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M)) : Set (V × V) :=
  {e | ∃ f ∈ (canonicalErasedRoute
      (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward,
    e.1 = f.1 ∨ e.2 = f.2}

/-- The valid one-route transaction in the maximal ordered active closure. -/
def maximalActiveRouteSwitchEdges
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M)) : Set (V × V) :=
  (canonicalErasedRepairedEdges (EqualInput L hL)
      (routesBeforeIndex L hL (ActiveWarp hL M)
        (warpPathIndex (L.popularAuxiliaryIndexed hL)
          (ActiveWarp hL M) p)) \
    maximalActiveRouteForwardConflictEdges hL p) ∪
  (canonicalErasedRoute
    (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward

/-- The active maximal subwarp has pairwise-disjoint decoded carriers. -/
theorem maximalOrderedActiveSubwarp_decodedCarriers_pairwiseDisjoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)) :
    (ActiveWarp hL M).paths.PairwiseDisjoint
      (EqualInput L hL).decodedVertexCarrier := by
  exact orderedActiveSubwarp_decodedCarriers_pairwiseDisjoint
    (EqualInput L hL) (L.popularAuxiliary_proxyPathsFaithful hL)
    (L.popularAuxiliaryIndexed hL)
    (L.popularAuxiliaryIndexed_sourceIndexed hL) (MaximalWarp M)

/-- Every strict active initial segment inherits decoded-carrier
disjointness. -/
theorem maximalActive_routesBeforeIndex_decodedDisjoint
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved))
    (a : Stationary.Below kappa) :
    (routesBeforeIndex L hL (ActiveWarp hL M) a).paths.PairwiseDisjoint
      (EqualInput L hL).decodedVertexCarrier := by
  intro p hp r hr hpr
  exact maximalOrderedActiveSubwarp_decodedCarriers_pairwiseDisjoint M
    hp.1 hr.1 hpr

/-- The lower-index repaired relation is locally bi-unique. -/
theorem maximalActive_repairedBeforeIndex_biUnique
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved))
    (a : Stationary.Below kappa) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
      (EqualInput L hL) (routesBeforeIndex L hL (ActiveWarp hL M) a)) :=
  canonicalErasedRepairedEdges_biUnique
    (EqualInput L hL) (routesBeforeIndex L hL (ActiveWarp hL M) a)
    (maximalActive_routesBeforeIndex_decodedDisjoint M a)

/-- The forward relation of one active route is locally bi-unique. -/
theorem maximalActive_routeForwardEdges_biUnique
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M)) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈
      (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward) := by
  have hfull := canonicalErasedForwardEdges_biUnique_of_decodedCarrierDisjoint
    (EqualInput L hL) (ActiveWarp hL M)
    (maximalOrderedActiveSubwarp_decodedCarriers_pairwiseDisjoint M)
  have hmem : ∀ {e : V × V}, e ∈
      (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward →
      e ∈ canonicalErasedForwardEdges (EqualInput L hL) (ActiveWarp hL M) := by
    intro e he
    simp only [canonicalErasedForwardEdges, Set.mem_iUnion]
    exact ⟨p, he⟩
  constructor
  · intro x y z hxz hyz
    exact hfull.1 (hmem hxz) (hmem hyz)
  · intro x y z hxy hxz
    exact hfull.2 (hmem hxy) (hmem hxz)

/-- Conflict deletion makes the one-route transaction locally bi-unique. -/
theorem maximalActiveRouteSwitchEdges_biUnique
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M)) :
    Relator.BiUnique
      (fun x y ↦ (x, y) ∈ maximalActiveRouteSwitchEdges hL p) := by
  let E₀ := canonicalErasedRepairedEdges (EqualInput L hL)
    (routesBeforeIndex L hL (ActiveWarp hL M)
      (warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) p))
  let F := (canonicalErasedRoute
    (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward
  have hbase : Relator.BiUnique (fun x y ↦
      (x, y) ∈ E₀ \ maximalActiveRouteForwardConflictEdges hL p) := by
    have hE₀ := maximalActive_repairedBeforeIndex_biUnique M
      (warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) p)
    constructor
    · intro x y z hxz hyz
      exact hE₀.1 hxz.1 hyz.1
    · intro x y z hxy hxz
      exact hE₀.2 hxy.1 hxz.1
  have hforward : Relator.BiUnique (fun x y ↦ (x, y) ∈ F) :=
    maximalActive_routeForwardEdges_biUnique p
  constructor
  · intro x y z hxz hyz
    rcases hxz with hxz | hxz <;> rcases hyz with hyz | hyz
    · exact hbase.1 hxz hyz
    · exfalso
      exact hxz.2 ⟨(y, z), hyz, Or.inr rfl⟩
    · exfalso
      exact hyz.2 ⟨(x, z), hxz, Or.inr rfl⟩
    · exact hforward.1 hxz hyz
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy <;> rcases hxz with hxz | hxz
    · exact hbase.2 hxy hxz
    · exfalso
      exact hxy.2 ⟨(x, z), hxz, Or.inl rfl⟩
    · exfalso
      exact hxz.2 ⟨(x, y), hxy, Or.inl rfl⟩
    · exact hforward.2 hxy hxz

/-- The one-route transaction consists only of ambient graph edges. -/
theorem maximalActiveRouteSwitchEdges_subset_adj
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M)) :
    maximalActiveRouteSwitchEdges hL p ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  rintro e (he | he)
  · exact canonicalErasedRepairedEdges_subset_adj
      (EqualInput L hL)
      (routesBeforeIndex L hL (ActiveWarp hL M)
        (warpPathIndex (L.popularAuxiliaryIndexed hL)
          (ActiveWarp hL M) p)) he.1
  · simp only [AltPath.directionEdges, Set.mem_iUnion] at he
    obtain ⟨l, _hl, _hdir, hel⟩ := he
    exact l.path.edgeSet_subset_adj hel

/-- A lower-index repaired edge that conflicts at an endpoint with a current
active forward edge is an original limiting-ladder edge.  In particular it
is not a forward edge inserted by a different earlier active route: decoded
carrier disjointness rules out the common endpoint. -/
theorem maximalActive_repairedBefore_mem_familyEdges_of_conflict_currentForward
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M)) {e f : V × V}
    (he : e ∈ canonicalErasedRepairedEdges (EqualInput L hL)
      (routesBeforeIndex L hL (ActiveWarp hL M)
        (warpPathIndex (L.popularAuxiliaryIndexed hL)
          (ActiveWarp hL M) p)))
    (hf : f ∈ (canonicalErasedRoute
      (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward)
    (hconflict : e.1 = f.1 ∨ e.2 = f.2) :
    e ∈ (EqualInput L hL).familyEdges := by
  let J := EqualInput L hL
  let a := warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) p
  let W := routesBeforeIndex L hL (ActiveWarp hL M) a
  rcases he with heResidual | heForward
  · exact heResidual.1.1
  · exfalso
    simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at heForward
    obtain ⟨r, hre⟩ := heForward
    obtain ⟨hrActive, hrlt⟩ := r.2
    let rActive : WarpPath (ActiveWarp hL M) := ⟨r.1, hrActive⟩
    have hrp : rActive ≠ p := by
      intro hrp
      have hindex := congrArg
        (warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M)) hrp
      exact (ne_of_lt hrlt) hindex
    have hdisj : Disjoint (J.decodedVertexCarrier r.1)
        (J.decodedVertexCarrier p.1) := by
      exact maximalOrderedActiveSubwarp_decodedCarriers_pairwiseDisjoint M
        hrActive p.2 (fun hval ↦ hrp (Subtype.ext hval))
    have hrEnds := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute J W r) hre
    have hpEnds := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute J (ActiveWarp hL M) p) hf
    have hrCarrier :=
      canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J W r
    have hpCarrier :=
      canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
        J (ActiveWarp hL M) p
    rcases hconflict with htail | hhead
    · have heq : e.1 ∈ J.decodedVertexCarrier p.1 := by
        rw [htail]
        exact hpCarrier hpEnds.1
      exact Set.disjoint_left.1 hdisj (hrCarrier hrEnds.1) heq
    · have heq : e.2 ∈ J.decodedVertexCarrier p.1 := by
        rw [hhead]
        exact hpCarrier hpEnds.2
      exact Set.disjoint_left.1 hdisj (hrCarrier hrEnds.2) heq

/-- At its own transaction, an active route's canonical source root either
survives conflict deletion, or the first deleted earlier edge and its
responsible current forward edge are displayed. -/
theorem maximalActive_routeInitial_rooted_or_switchConflict
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M))
    (R : L.CanonicalErasedRouteRootPrefix hL (ActiveWarp hL M) p) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ maximalActiveRouteSwitchEdges hL p) a
        (canonicalErasedRoute
          (EqualInput L hL) (ActiveWarp hL M) p).initial) ∨
    (∃ a ∈ Gamma.source, ∃ u v f,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ maximalActiveRouteSwitchEdges hL p) a u ∧
      (u, v) ∈ canonicalErasedRepairedEdges (EqualInput L hL)
        (routesBeforeIndex L hL (ActiveWarp hL M)
          (warpPathIndex (L.popularAuxiliaryIndexed hL)
            (ActiveWarp hL M) p)) ∧
      f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward ∧
      ((u, v).1 = f.1 ∨ (u, v).2 = f.2) ∧
      (u, v) ∉ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward) := by
  obtain ⟨a, ha, hroot⟩ := maximalActive_route_initial_sourceRooted_before_self p R
  let base := canonicalErasedRepairedEdges (EqualInput L hL)
    (routesBeforeIndex L hL (ActiveWarp hL M)
      (warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) p))
  let inserted := (canonicalErasedRoute
    (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward
  let blocked := maximalActiveRouteForwardConflictEdges hL p
  have hrootUnion : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ base ∪ inserted) a
      (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).initial :=
    Relation.ReflTransGen.mono (fun _ _ hxy ↦ Or.inl hxy) _ _ hroot
  rcases
      OrderedReservedStationaryDiagonalEqualSelection.reflTransGen_union_prune_or_exists_conflict
        hrootUnion with hsurvives |
        ⟨u, v, hau, huvBase, huvBlocked, huvNotInserted⟩
  · left
    refine ⟨a, ha, ?_⟩
    simpa only [maximalActiveRouteSwitchEdges, base, inserted, blocked] using
      hsurvives
  · right
    obtain ⟨f, hf, hconflict⟩ := huvBlocked
    refine ⟨a, ha, u, v, f, ?_, huvBase, hf, hconflict, huvNotInserted⟩
    simpa only [maximalActiveRouteSwitchEdges, base, inserted, blocked] using hau

/-- The same-tail half of a displayed switch conflict is already absorbed:
the rooted old tail traverses the inserted current forward edge.  Thus the
only genuinely unabsorbed initial-root obstruction is a same-head conflict. -/
theorem maximalActive_routeInitial_rooted_or_forwardHeadRooted_or_sameHeadConflict
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M))
    (R : L.CanonicalErasedRouteRootPrefix hL (ActiveWarp hL M) p) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ maximalActiveRouteSwitchEdges hL p) a
        (canonicalErasedRoute
          (EqualInput L hL) (ActiveWarp hL M) p).initial) ∨
    (∃ f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ maximalActiveRouteSwitchEdges hL p)
          a f.2) ∨
    (∃ a ∈ Gamma.source, ∃ u v f,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ maximalActiveRouteSwitchEdges hL p) a u ∧
      (u, v) ∈ canonicalErasedRepairedEdges (EqualInput L hL)
        (routesBeforeIndex L hL (ActiveWarp hL M)
          (warpPathIndex (L.popularAuxiliaryIndexed hL)
            (ActiveWarp hL M) p)) ∧
      f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward ∧
      v = f.2 ∧
      (u, v) ∉ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward) := by
  rcases maximalActive_routeInitial_rooted_or_switchConflict p R with
      hroot | ⟨a, ha, u, v, f, hau, huv, hf, htail | hhead, hnot⟩
  · exact Or.inl hroot
  · right
    left
    refine ⟨f, hf, a, ha, hau.trans (.single ?_)⟩
    apply Or.inr
    change u = f.1 at htail
    rw [htail]
    exact hf
  · right
    right
    exact ⟨a, ha, u, v, f, hau, huv, hf, hhead, hnot⟩

/-- In the only unabsorbed switch case, the rooted old tail belongs to a
specific limiting-ladder component exposed by the current active route.
Thus the obstruction is no longer an anonymous relation collision: it is
an ordered active-closure contact with an ambient ladder owner. -/
theorem maximalActive_routeInitial_rooted_or_forwardHeadRooted_or_exposedParentConflict
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M))
    (R : L.CanonicalErasedRouteRootPrefix hL (ActiveWarp hL M) p) :
    (∃ a ∈ Gamma.source,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ maximalActiveRouteSwitchEdges hL p) a
        (canonicalErasedRoute
          (EqualInput L hL) (ActiveWarp hL M) p).initial) ∨
    (∃ f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ maximalActiveRouteSwitchEdges hL p)
          a f.2) ∨
    (∃ a ∈ Gamma.source, ∃ u v f, ∃ Y : Gamma.DPath,
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ maximalActiveRouteSwitchEdges hL p) a u ∧
      (u, v) ∈ Y.edgeSet ∧
      Y ∈ (EqualInput L hL).ladder.paths ∧
      Y ∈ GroundingSimultaneousDecode.exposedLadderPaths
        (EqualInput L hL) p.1 ∧
      f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward ∧
      v = f.2 ∧
      (u, v) ∉ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward) := by
  rcases maximalActive_routeInitial_rooted_or_forwardHeadRooted_or_sameHeadConflict
      p R with hroot | hforward | hconflict
  · exact Or.inl hroot
  · exact Or.inr (Or.inl hforward)
  · right
    right
    obtain ⟨a, ha, u, v, f, hau, huv, hf, hvf, hnot⟩ := hconflict
    have huvFamily : (u, v) ∈ (EqualInput L hL).familyEdges :=
      maximalActive_repairedBefore_mem_familyEdges_of_conflict_currentForward
        p huv hf (Or.inr hvf)
    obtain ⟨Y, hY, huvY⟩ := huvFamily
    have hvCarrier : v ∈ (EqualInput L hL).decodedVertexCarrier p.1 := by
      have hfEnds := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p) hf
      apply canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
        (EqualInput L hL) (ActiveWarp hL M) p
      rw [hvf]
      exact hfEnds.2
    have hvY : v ∈ Y.support :=
      (Y.edgeSet_subset_support_prod huvY).2
    have hYExposed : Y ∈
        GroundingSimultaneousDecode.exposedLadderPaths
          (EqualInput L hL) p.1 := by
      apply (EqualInput L hL).mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
        (L.popularAuxiliary_proxyPathsFaithful hL) p.1
        ((ActiveWarp hL M).starts_in_source p.2) hY hvCarrier hvY
    exact ⟨a, ha, u, v, f, Y, hau, huvY, hY, hYExposed, hf, hvf, hnot⟩

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.maximalActiveRouteSwitchEdges_biUnique
#print axioms Erdos599.DWeb.KappaLadder.maximalActiveRouteSwitchEdges_subset_adj
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_routeInitial_rooted_or_switchConflict
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_routeInitial_rooted_or_forwardHeadRooted_or_sameHeadConflict
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_routeInitial_rooted_or_forwardHeadRooted_or_exposedParentConflict
