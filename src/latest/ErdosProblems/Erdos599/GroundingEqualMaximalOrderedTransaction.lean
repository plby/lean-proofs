/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalOrderedRouteSwitch
import ErdosProblems.Erdos599.GroundingEqualOrderedTransaction
import ErdosProblems.Erdos599.GroundingEqualMinimalTargetPreStoppedCompiler

/-!
# Sound ordered transactions in the maximal active closure

The endpoint-repaired one-route relation is useful for isolating forward
conflicts, but the canonical post-transaction relation must also remove the
current route's backward edges.  This file works with that literal relation:
the canonical repaired relation of all active routes through the current
source index.  It proves the exact deletion classification and transfers the
grounded input root up to the first deleted current edge.
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

private abbrev ActiveWarp
    {L : Gamma.KappaLadder kappa} (hL : L.IsKappaHindrance)
    {q : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :=
  maximalOrderedActiveSubwarp hL M

/-- Active maximal routes processed no later than `a`. -/
def maximalActiveRoutesThroughIndex
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved))
    (a : Stationary.Below kappa) :
    Popular.XSWarp
      (EqualInput L hL).lambda (EqualInput L hL).lambda.target where
  paths := {p | ∃ hp : p ∈ (ActiveWarp hL M).paths,
    warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M)
      ⟨p, hp⟩ ≤ a}
  disjoint := by
    rintro p ⟨hp, _⟩ q ⟨hq, _⟩ hpq
    exact (ActiveWarp hL M).disjoint hp hq hpq
  starts_in_source := by
    rintro p ⟨hp, _⟩
    exact (ActiveWarp hL M).starts_in_source hp
  ends_in_target := by
    rintro p ⟨hp, _⟩
    exact (ActiveWarp hL M).ends_in_target hp

theorem maximalActiveRoutesThroughIndex_paths_subset
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved))
    (a : Stationary.Below kappa) :
    (maximalActiveRoutesThroughIndex L hL M a).paths ⊆
      (ActiveWarp hL M).paths := by
  rintro p ⟨hp, _⟩
  exact hp

theorem maximalActive_mem_routesThroughIndex_self
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M)) :
    p.1 ∈ (maximalActiveRoutesThroughIndex L hL M
      (warpPathIndex (L.popularAuxiliaryIndexed hL)
        (ActiveWarp hL M) p)).paths :=
  ⟨p.2, le_rfl⟩

theorem maximalActive_routesBeforeIndex_paths_subset_routesThroughIndex
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved))
    (a : Stationary.Below kappa) :
    (routesBeforeIndex L hL (ActiveWarp hL M) a).paths ⊆
      (maximalActiveRoutesThroughIndex L hL M a).paths := by
  rintro p ⟨hp, hpa⟩
  exact ⟨hp, hpa.le⟩

theorem maximalActive_routesThroughIndex_eq_current_or_mem_before
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M))
    (r : WarpPath (maximalActiveRoutesThroughIndex L hL M
      (warpPathIndex (L.popularAuxiliaryIndexed hL)
        (ActiveWarp hL M) p))) :
    r.1 = p.1 ∨ r.1 ∈ (routesBeforeIndex L hL (ActiveWarp hL M)
      (warpPathIndex (L.popularAuxiliaryIndexed hL)
        (ActiveWarp hL M) p)).paths := by
  obtain ⟨hr, hrle⟩ := r.2
  rcases lt_or_eq_of_le hrle with hrlt | hreq
  · exact Or.inr ⟨hr, hrlt⟩
  · left
    have hrp : (⟨r.1, hr⟩ : WarpPath (ActiveWarp hL M)) = p := by
      apply warpPath_eq_of_index_eq
        (L.popularAuxiliaryIndexed hL)
        (L.popularAuxiliaryIndexed_sourceIndexed hL) (ActiveWarp hL M)
      exact hreq
    exact congrArg Subtype.val hrp

/-- The literal through-index relation is adjacent and bi-unique. -/
theorem maximalActive_routesThroughIndex_repairedEdges_biUnique
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved))
    (a : Stationary.Below kappa) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
      (EqualInput L hL) (maximalActiveRoutesThroughIndex L hL M a)) := by
  apply canonicalErasedRepairedEdges_biUnique
  intro p hp r hr hpr
  exact maximalOrderedActiveSubwarp_decodedCarriers_pairwiseDisjoint M
    (maximalActiveRoutesThroughIndex_paths_subset M a hp)
    (maximalActiveRoutesThroughIndex_paths_subset M a hr) hpr

theorem maximalActive_routesThroughIndex_repairedEdges_subset_adj
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved))
    (a : Stationary.Below kappa) :
    canonicalErasedRepairedEdges (EqualInput L hL)
      (maximalActiveRoutesThroughIndex L hL M a) ⊆
        {e | Gamma.graph.Adj e.1 e.2} :=
  canonicalErasedRepairedEdges_subset_adj (EqualInput L hL)
    (maximalActiveRoutesThroughIndex L hL M a)

/-- Every current forward edge is inserted in the literal post-transaction
relation. -/
theorem maximalActive_current_forwardEdges_subset_routesThroughIndex_repaired
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M)) :
    (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p
      ).directionEdges .forward ⊆
      canonicalErasedRepairedEdges (EqualInput L hL)
        (maximalActiveRoutesThroughIndex L hL M
          (warpPathIndex (L.popularAuxiliaryIndexed hL)
            (ActiveWarp hL M) p)) := by
  intro e he
  apply Or.inr
  simp only [canonicalErasedForwardEdges, Set.mem_iUnion]
  let pT : WarpPath (maximalActiveRoutesThroughIndex L hL M
      (warpPathIndex (L.popularAuxiliaryIndexed hL)
        (ActiveWarp hL M) p)) :=
    ⟨p.1, maximalActive_mem_routesThroughIndex_self p⟩
  refine ⟨pT, ?_⟩
  simpa only [pT, canonicalErasedRoute] using he

/-- An edge lost at the current literal transaction is either a current
backward edge or has a current forward endpoint conflict. -/
theorem maximalActive_mem_current_backward_or_forwardConflict_of_mem_before_not_mem_through
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M)) {e : V × V}
    (heBefore : e ∈ canonicalErasedRepairedEdges (EqualInput L hL)
      (routesBeforeIndex L hL (ActiveWarp hL M)
        (warpPathIndex (L.popularAuxiliaryIndexed hL)
          (ActiveWarp hL M) p)))
    (heNotThrough : e ∉ canonicalErasedRepairedEdges (EqualInput L hL)
      (maximalActiveRoutesThroughIndex L hL M
        (warpPathIndex (L.popularAuxiliaryIndexed hL)
          (ActiveWarp hL M) p))) :
    e ∈ (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p
      ).directionEdges .backward ∨
      ∃ f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward,
        e.1 = f.1 ∨ e.2 = f.2 := by
  let J := EqualInput L hL
  let U := L.popularAuxiliaryIndexed hL
  let B := routesBeforeIndex L hL (ActiveWarp hL M)
    (warpPathIndex U (ActiveWarp hL M) p)
  let T := maximalActiveRoutesThroughIndex L hL M
    (warpPathIndex U (ActiveWarp hL M) p)
  have heNotForwardB : e ∉ canonicalErasedForwardEdges J B := by
    intro heForward
    apply heNotThrough
    apply Or.inr
    simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at heForward ⊢
    obtain ⟨r, hr⟩ := heForward
    let rT : WarpPath T :=
      ⟨r.1, maximalActive_routesBeforeIndex_paths_subset_routesThroughIndex
        M (warpPathIndex U (ActiveWarp hL M) p) r.2⟩
    refine ⟨rT, ?_⟩
    simpa only [rT, canonicalErasedRoute] using hr
  have heBase : e ∈ canonicalErasedResidualEdges J B \
      canonicalErasedForwardConflictEdges J B := by
    rcases heBefore with heBase | heForward
    · exact heBase
    · exact False.elim (heNotForwardB heForward)
  have heFamily : e ∈ J.familyEdges := heBase.1.1
  by_cases heBackwardT : e ∈ canonicalErasedBackwardEdges J T
  · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackwardT
    obtain ⟨r, hr⟩ := heBackwardT
    rcases maximalActive_routesThroughIndex_eq_current_or_mem_before p r with
      hrp | hrB
    · left
      have hroute : canonicalErasedRoute J T r =
          canonicalErasedRoute J (ActiveWarp hL M) p :=
        OrderedReservedStationaryDiagonalEqualSelection.canonicalErasedRoute_eq_of_path_eq
          J hrp
      rw [hroute] at hr
      simpa only [J] using hr
    · exfalso
      exact heBase.1.2 (by
        simp only [canonicalErasedBackwardEdges, Set.mem_iUnion]
        exact ⟨⟨r.1, hrB⟩, by
          simpa only [canonicalErasedRoute] using hr⟩)
  · have heResidualT : e ∈ canonicalErasedResidualEdges J T :=
      ⟨heFamily, heBackwardT⟩
    have heConflictT : e ∈ canonicalErasedForwardConflictEdges J T := by
      by_contra heNotConflict
      exact heNotThrough (Or.inl ⟨heResidualT, heNotConflict⟩)
    obtain ⟨f, hf, hends⟩ := heConflictT
    simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
    obtain ⟨r, hrf⟩ := hf
    rcases maximalActive_routesThroughIndex_eq_current_or_mem_before p r with
      hrp | hrB
    · right
      have hroute : canonicalErasedRoute J T r =
          canonicalErasedRoute J (ActiveWarp hL M) p :=
        OrderedReservedStationaryDiagonalEqualSelection.canonicalErasedRoute_eq_of_path_eq
          J hrp
      rw [hroute] at hrf
      exact ⟨f, by simpa only [J] using hrf, hends⟩
    · exfalso
      exact heBase.2 ⟨f, by
        simp only [canonicalErasedForwardEdges, Set.mem_iUnion]
        exact ⟨⟨r.1, hrB⟩, by
          simpa only [canonicalErasedRoute] using hrf⟩, hends⟩

/-- At the sound post-transaction relation the grounded initial survives,
or the first lost source-prefix edge is a precisely classified current
backward/forward-conflict deletion and its tail is still source-rooted. -/
theorem maximalActive_routeInitial_rooted_through_or_currentDeletion
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
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges (EqualInput L hL)
          (maximalActiveRoutesThroughIndex L hL M
            (warpPathIndex (L.popularAuxiliaryIndexed hL)
              (ActiveWarp hL M) p))) a
        (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p).initial) ∨
    (∃ (a u v : V), a ∈ Gamma.source ∧
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges (EqualInput L hL)
          (maximalActiveRoutesThroughIndex L hL M
            (warpPathIndex (L.popularAuxiliaryIndexed hL)
              (ActiveWarp hL M) p))) a u ∧
      (u, v) ∈ canonicalErasedRepairedEdges (EqualInput L hL)
        (routesBeforeIndex L hL (ActiveWarp hL M)
          (warpPathIndex (L.popularAuxiliaryIndexed hL)
            (ActiveWarp hL M) p)) ∧
      ((u, v) ∈ (canonicalErasedRoute
          (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .backward ∨
        ∃ f ∈ (canonicalErasedRoute
          (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward,
          u = f.1 ∨ v = f.2) ∧
      (u, v) ∉ canonicalErasedRepairedEdges (EqualInput L hL)
        (maximalActiveRoutesThroughIndex L hL M
          (warpPathIndex (L.popularAuxiliaryIndexed hL)
            (ActiveWarp hL M) p))) := by
  obtain ⟨a, ha, hroot⟩ :=
    maximalActive_route_initial_sourceRooted_before_self p R
  let B := canonicalErasedRepairedEdges (EqualInput L hL)
    (routesBeforeIndex L hL (ActiveWarp hL M)
      (warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) p))
  let T := canonicalErasedRepairedEdges (EqualInput L hL)
    (maximalActiveRoutesThroughIndex L hL M
      (warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) p))
  let blocked : Set (V × V) := B \ T
  have hrootUnion : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ B ∪ (∅ : Set (V × V))) a
      (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p).initial :=
    Relation.ReflTransGen.mono (fun _ _ hxy ↦ Or.inl hxy) _ _ hroot
  rcases
      OrderedReservedStationaryDiagonalEqualSelection.reflTransGen_union_prune_or_exists_conflict
        (blocked := blocked) hrootUnion with hsurvives |
        ⟨u, v, hau, huvB, huvBlocked, _huvNotEmpty⟩
  · left
    refine ⟨a, ha, Relation.ReflTransGen.mono ?_ _ _ hsurvives⟩
    intro x y hxy
    rcases hxy with hxy | hxy
    · by_contra hnotT
      exact hxy.2 ⟨hxy.1, hnotT⟩
    · exact False.elim hxy
  · right
    have huvNotT : (u, v) ∉ T := huvBlocked.2
    have hclassified :=
      maximalActive_mem_current_backward_or_forwardConflict_of_mem_before_not_mem_through
        p huvB huvNotT
    refine ⟨a, u, v, ha, Relation.ReflTransGen.mono ?_ _ _ hau,
      huvB, hclassified, huvNotT⟩
    intro x y hxy
    rcases hxy with hxy | hxy
    · by_contra hnotT
      exact hxy.2 ⟨hxy.1, hnotT⟩
    · exact False.elim hxy

/-- Every active transaction produces a concrete rooted absorption seed.
It is either an actual vertex of the current erased route, or a point on a
limiting-ladder component exposed by that route.  The latter alternative is
exactly the same-head case: the surviving rooted tail belongs to the old
ladder edge entering the current forward head. -/
theorem maximalActive_exists_sourceRooted_routeVertex_or_exposedParentPoint_through
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M))
    (R : L.CanonicalErasedRouteRootPrefix hL (ActiveWarp hL M) p) :
    (∃ x ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).vertexSet,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun s t ↦ (s, t) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL)
            (maximalActiveRoutesThroughIndex L hL M
              (warpPathIndex (L.popularAuxiliaryIndexed hL)
                (ActiveWarp hL M) p))) a x) ∨
    (∃ Y : Gamma.DPath,
      Y ∈ (EqualInput L hL).ladder.paths ∧
      Y ∈ GroundingSimultaneousDecode.exposedLadderPaths
        (EqualInput L hL) p.1 ∧
      ∃ x ∈ Y.support, ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun s t ↦ (s, t) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL)
            (maximalActiveRoutesThroughIndex L hL M
              (warpPathIndex (L.popularAuxiliaryIndexed hL)
                (ActiveWarp hL M) p))) a x) := by
  rcases maximalActive_routeInitial_rooted_through_or_currentDeletion p R with
      hroot | hdeleted
  · left
    obtain ⟨a, ha, hax⟩ := hroot
    exact ⟨_, (canonicalErasedRoute
      (EqualInput L hL) (ActiveWarp hL M) p).initial_mem_vertexSet,
      a, ha, hax⟩
  · obtain ⟨a, u, v, ha, hau, huvBefore, hkind, _huvNotThrough⟩ := hdeleted
    rcases hkind with hbackward | ⟨f, hf, htail | hhead⟩
    · left
      have huvEnds := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p)
        hbackward
      exact ⟨u, huvEnds.1, a, ha, hau⟩
    · left
      have hfEnds := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p) hf
      exact ⟨u, htail ▸ hfEnds.1, a, ha, hau⟩
    · right
      have huvFamily : (u, v) ∈ (EqualInput L hL).familyEdges :=
        maximalActive_repairedBefore_mem_familyEdges_of_conflict_currentForward
          p huvBefore hf (Or.inr hhead)
      obtain ⟨Y, hY, huvY⟩ := huvFamily
      have hvCarrier : v ∈ (EqualInput L hL).decodedVertexCarrier p.1 := by
        have hfEnds := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p) hf
        apply canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
          (EqualInput L hL) (ActiveWarp hL M) p
        rw [hhead]
        exact hfEnds.2
      have hvY : v ∈ Y.support := (Y.edgeSet_subset_support_prod huvY).2
      have hYExposed : Y ∈
          GroundingSimultaneousDecode.exposedLadderPaths
            (EqualInput L hL) p.1 := by
        apply (EqualInput L hL).mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
          (L.popularAuxiliary_proxyPathsFaithful hL) p.1
          ((ActiveWarp hL M).starts_in_source p.2) hY hvCarrier hvY
      exact ⟨Y, hY, hYExposed, u,
        (Y.edgeSet_subset_support_prod huvY).1, a, ha, hau⟩

/-- On the grounded parent of an active route, every edge deleted by the
full active repaired relation is deleted by that route itself.  Other active
routes have decoded carrier disjoint from the whole parent. -/
theorem maximalActive_rootParentEdge_currentDeletion_of_not_mem_full
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M))
    (R : L.CanonicalErasedRouteRootPrefix hL (ActiveWarp hL M) p)
    {e : V × V} (heParent : e ∈ R.parent.edgeSet)
    (heNotFull : e ∉ canonicalErasedRepairedEdges
      (EqualInput L hL) (ActiveWarp hL M)) :
    e ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .backward ∨
      ∃ f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward,
        e.1 = f.1 ∨ e.2 = f.2 := by
  let J := EqualInput L hL
  have heFamily : e ∈ J.familyEdges := by
    refine ⟨R.parent, ?_, heParent⟩
    simpa only [J, EqualInput, KappaLadder.popularAuxiliaryInput] using
      R.parent_inessential.1
  by_cases heBackward : e ∈ canonicalErasedBackwardEdges J (ActiveWarp hL M)
  · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackward
    obtain ⟨r, her⟩ := heBackward
    have hrp : r = p := by
      by_contra hne
      have hdisj := maximalActive_otherRoute_decodedCarrier_disjoint_rootParent
        r p hne R
      have hrEnds := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute J (ActiveWarp hL M) r) her
      have hrCarrier :=
        canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
          J (ActiveWarp hL M) r hrEnds.1
      exact Set.disjoint_left.1 hdisj hrCarrier
        (R.parent.edgeSet_subset_support_prod heParent).1
    left
    subst r
    exact her
  · have heResidual : e ∈ canonicalErasedResidualEdges J (ActiveWarp hL M) :=
      ⟨heFamily, heBackward⟩
    have heConflict : e ∈
        canonicalErasedForwardConflictEdges J (ActiveWarp hL M) := by
      by_contra heNotConflict
      exact heNotFull (Or.inl ⟨heResidual, heNotConflict⟩)
    obtain ⟨f, hf, htail | hhead⟩ := heConflict
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      have hrp : r = p := by
        by_contra hne
        have hdisj := maximalActive_otherRoute_decodedCarrier_disjoint_rootParent
          r p hne R
        have hrEnds := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J (ActiveWarp hL M) r) hfr
        have hrCarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
            J (ActiveWarp hL M) r hrEnds.1
        exact Set.disjoint_left.1 hdisj hrCarrier
          (htail ▸ (R.parent.edgeSet_subset_support_prod heParent).1)
      right
      subst r
      exact ⟨f, hfr, Or.inl htail⟩
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      have hrp : r = p := by
        by_contra hne
        have hdisj := maximalActive_otherRoute_decodedCarrier_disjoint_rootParent
          r p hne R
        have hrEnds := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J (ActiveWarp hL M) r) hfr
        have hrCarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
            J (ActiveWarp hL M) r hrEnds.2
        exact Set.disjoint_left.1 hdisj hrCarrier
          (hhead ▸ (R.parent.edgeSet_subset_support_prod heParent).2)
      right
      subst r
      exact ⟨f, hfr, Or.inr hhead⟩

/-- A limiting component exposed and actually met by an active route is
isolated from every other active decoded carrier.  A later route avoids the
component directly.  If an earlier route met it, that earlier route would
also expose it, forcing the current later route to avoid its own contact. -/
theorem maximalActive_otherRoute_decodedCarrier_disjoint_exposedParent
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p r : WarpPath (ActiveWarp hL M)) (hrp : r ≠ p)
    {Y : Gamma.DPath}
    (hY : Y ∈ GroundingSimultaneousDecode.exposedLadderPaths
      (EqualInput L hL) p.1)
    (hself : ((EqualInput L hL).decodedVertexCarrier p.1 ∩
      Y.support).Nonempty) :
    Disjoint ((EqualInput L hL).decodedVertexCarrier r.1) Y.support := by
  have hindexNe :
      warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) r ≠
        warpPathIndex (L.popularAuxiliaryIndexed hL) (ActiveWarp hL M) p := by
    intro heq
    exact hrp (warpPath_eq_of_index_eq
      (L.popularAuxiliaryIndexed hL)
      (L.popularAuxiliaryIndexed_sourceIndexed hL)
      (ActiveWarp hL M) heq)
  rcases lt_or_gt_of_ne hindexNe with hrlt | hplt
  · rw [Set.disjoint_left]
    intro x hxr hxY
    have hYLadder : Y ∈ (EqualInput L hL).ladder.paths :=
      GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
        (L.popularAuxiliary_proxyPathsFaithful hL) p.1 hY
    have hYExposedR : Y ∈
        GroundingSimultaneousDecode.exposedLadderPaths
          (EqualInput L hL) r.1 := by
      apply (EqualInput L hL).mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
        (L.popularAuxiliary_proxyPathsFaithful hL) r.1
        ((ActiveWarp hL M).starts_in_source r.2) hYLadder hxr hxY
    have hpAvoid :=
      maximalActive_later_decodedCarrier_disjoint_earlier_exposedParent
        p r hrlt hYExposedR
    obtain ⟨z, hzp, hzY⟩ := hself
    exact Set.disjoint_left.1 hpAvoid hzp hzY
  · exact maximalActive_later_decodedCarrier_disjoint_earlier_exposedParent
      r p hplt hY

/-- In particular, the limiting owner of any current backward link is
untouched by every other active route. -/
theorem maximalActive_otherRoute_decodedCarrier_disjoint_backwardOwner
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p r : WarpPath (ActiveWarp hL M)) (hrp : r ≠ p)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (EqualInput L hL) (ActiveWarp hL M) p).links)
    (hldir : l.direction = .backward)
    (Y : Gamma.DPath) (hY : Y ∈ (EqualInput L hL).ladder.paths)
    (hsub : l.path.IsSubpathOf Y) :
    Disjoint ((EqualInput L hL).decodedVertexCarrier r.1) Y.support := by
  have hentryRoute : l.entry ∈ (canonicalErasedRoute
      (EqualInput L hL) (ActiveWarp hL M) p).vertexSet :=
    (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p
      ).link_support_subset_vertexSet hl l.entry_mem_support
  have hentryCarrier : l.entry ∈
      (EqualInput L hL).decodedVertexCarrier p.1 :=
    canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
      (EqualInput L hL) (ActiveWarp hL M) p hentryRoute
  have hentryY : l.entry ∈ Y.support := hsub.1 l.entry_mem_support
  have hYExposed : Y ∈
      GroundingSimultaneousDecode.exposedLadderPaths
        (EqualInput L hL) p.1 := by
    apply (EqualInput L hL).mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
      (L.popularAuxiliary_proxyPathsFaithful hL) p.1
      ((ActiveWarp hL M).starts_in_source p.2) hY hentryCarrier hentryY
  exact maximalActive_otherRoute_decodedCarrier_disjoint_exposedParent
    p r hrp hYExposed ⟨l.entry, hentryCarrier, hentryY⟩

/-- On any limiting component exposed and met by `p`, every deletion from
the full active relation is again a self-deletion of `p`. -/
theorem maximalActive_exposedParentEdge_currentDeletion_of_not_mem_full
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M))
    (Y : Gamma.DPath)
    (hY : Y ∈ GroundingSimultaneousDecode.exposedLadderPaths
      (EqualInput L hL) p.1)
    (hself : ((EqualInput L hL).decodedVertexCarrier p.1 ∩
      Y.support).Nonempty)
    {e : V × V} (heY : e ∈ Y.edgeSet)
    (heNotFull : e ∉ canonicalErasedRepairedEdges
      (EqualInput L hL) (ActiveWarp hL M)) :
    e ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .backward ∨
      ∃ f ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward,
        e.1 = f.1 ∨ e.2 = f.2 := by
  let J := EqualInput L hL
  have hYLadder : Y ∈ J.ladder.paths :=
    GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
      (L.popularAuxiliary_proxyPathsFaithful hL) p.1 hY
  have heFamily : e ∈ J.familyEdges := ⟨Y, hYLadder, heY⟩
  by_cases heBackward : e ∈ canonicalErasedBackwardEdges J (ActiveWarp hL M)
  · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackward
    obtain ⟨r, her⟩ := heBackward
    have hrp : r = p := by
      by_contra hne
      have hdisj := maximalActive_otherRoute_decodedCarrier_disjoint_exposedParent
        p r hne hY hself
      have hrEnds := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute J (ActiveWarp hL M) r) her
      have hrCarrier :=
        canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
          J (ActiveWarp hL M) r hrEnds.1
      exact Set.disjoint_left.1 hdisj hrCarrier
        (Y.edgeSet_subset_support_prod heY).1
    left
    subst r
    exact her
  · have heResidual : e ∈ canonicalErasedResidualEdges J (ActiveWarp hL M) :=
      ⟨heFamily, heBackward⟩
    have heConflict : e ∈
        canonicalErasedForwardConflictEdges J (ActiveWarp hL M) := by
      by_contra heNotConflict
      exact heNotFull (Or.inl ⟨heResidual, heNotConflict⟩)
    obtain ⟨f, hf, htail | hhead⟩ := heConflict
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      have hrp : r = p := by
        by_contra hne
        have hdisj := maximalActive_otherRoute_decodedCarrier_disjoint_exposedParent
          p r hne hY hself
        have hrEnds := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J (ActiveWarp hL M) r) hfr
        have hrCarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
            J (ActiveWarp hL M) r hrEnds.1
        exact Set.disjoint_left.1 hdisj hrCarrier
          (htail ▸ (Y.edgeSet_subset_support_prod heY).1)
      right
      subst r
      exact ⟨f, hfr, Or.inl htail⟩
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      have hrp : r = p := by
        by_contra hne
        have hdisj := maximalActive_otherRoute_decodedCarrier_disjoint_exposedParent
          p r hne hY hself
        have hrEnds := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute J (ActiveWarp hL M) r) hfr
        have hrCarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
            J (ActiveWarp hL M) r hrEnds.2
        exact Set.disjoint_left.1 hdisj hrCarrier
          (hhead ▸ (Y.edgeSet_subset_support_prod heY).2)
      right
      subst r
      exact ⟨f, hfr, Or.inr hhead⟩

/-- The full simultaneous active relation already produces a source-rooted
geometric absorption seed for every active route.  This is the global form
of the transaction lemma: later active routes cannot create a new deletion
on the route's grounded parent. -/
theorem maximalActive_exists_sourceRooted_routeVertex_or_exposedParentPoint_full
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {reserved : FinitePath (EqualInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {reserved.start})
      (collisionCarrier (EqualInput L hL) reserved)}
    (p : WarpPath (ActiveWarp hL M))
    (R : L.CanonicalErasedRouteRootPrefix hL (ActiveWarp hL M) p) :
    (∃ x ∈ (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).vertexSet,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun s t ↦ (s, t) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (ActiveWarp hL M)) a x) ∨
    (∃ Y : Gamma.DPath,
      Y ∈ (EqualInput L hL).ladder.paths ∧
      Y ∈ GroundingSimultaneousDecode.exposedLadderPaths
        (EqualInput L hL) p.1 ∧
      ∃ x ∈ Y.support, ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun s t ↦ (s, t) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (ActiveWarp hL M)) a x) := by
  let E := canonicalErasedRepairedEdges (EqualInput L hL) (ActiveWarp hL M)
  let inserted := (canonicalErasedRoute
    (EqualInput L hL) (ActiveWarp hL M) p).directionEdges .forward
  let blocked : Set (V × V) := R.path.edgeSet \ E
  have hpathReach : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ R.path.edgeSet) R.path.start R.path.finish :=
    GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
      R.path (fun _ h ↦ h) R.path.finish_mem_support
  have hrootUnion : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ R.path.edgeSet ∪ inserted)
      R.path.start R.path.finish :=
    Relation.ReflTransGen.mono (fun _ _ hxy ↦ Or.inl hxy) _ _ hpathReach
  rcases
      OrderedReservedStationaryDiagonalEqualSelection.reflTransGen_union_prune_or_exists_conflict
        (blocked := blocked) hrootUnion with hsurvives |
        ⟨u, v, hau, huvPath, huvBlocked, huvNotInserted⟩
  · left
    refine ⟨(canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).initial,
      (canonicalErasedRoute
        (EqualInput L hL) (ActiveWarp hL M) p).initial_mem_vertexSet,
      R.path.start, ?_, ?_⟩
    · exact R.start_mem_source
    · have hmono : (R.path.edgeSet \ blocked) ∪ inserted ⊆ E := by
        rintro e (he | he)
        · by_contra heNotE
          exact he.2 ⟨he.1, heNotE⟩
        · apply Or.inr
          simp only [canonicalErasedForwardEdges, Set.mem_iUnion]
          exact ⟨p, he⟩
      have hreach := Relation.ReflTransGen.mono
        (fun _ _ hxy ↦ hmono hxy) _ _ hsurvives
      simpa only [E, R.finish_eq] using hreach
  · have huvNotE : (u, v) ∉ E := huvBlocked.2
    have huvParent : (u, v) ∈ R.parent.edgeSet := R.edgeSet_subset huvPath
    have hkind := maximalActive_rootParentEdge_currentDeletion_of_not_mem_full
      p R huvParent huvNotE
    have hmono : (R.path.edgeSet \ blocked) ∪ inserted ⊆ E := by
      rintro e (he | he)
      · by_contra heNotE
        exact he.2 ⟨he.1, heNotE⟩
      · apply Or.inr
        simp only [canonicalErasedForwardEdges, Set.mem_iUnion]
        exact ⟨p, he⟩
    have hauE := Relation.ReflTransGen.mono
      (fun _ _ hxy ↦ hmono hxy) _ _ hau
    have haSource : R.path.start ∈ Gamma.source := R.start_mem_source
    rcases hkind with hbackward | ⟨f, hf, htail | hhead⟩
    · left
      have hEnds := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p)
        hbackward
      exact ⟨u, hEnds.1, R.path.start, haSource, hauE⟩
    · left
      have hEnds := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p) hf
      change u = f.1 at htail
      exact ⟨u, htail.symm ▸ hEnds.1, R.path.start, haSource, hauE⟩
    · right
      have huvFamily : (u, v) ∈ (EqualInput L hL).familyEdges := by
        refine ⟨R.parent, ?_, huvParent⟩
        simpa only [EqualInput, KappaLadder.popularAuxiliaryInput] using
          R.parent_inessential.1
      obtain ⟨Y, hY, huvY⟩ := huvFamily
      have hvCarrier : v ∈ (EqualInput L hL).decodedVertexCarrier p.1 := by
        have hfEnds := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute (EqualInput L hL) (ActiveWarp hL M) p) hf
        apply canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
          (EqualInput L hL) (ActiveWarp hL M) p
        change v = f.2 at hhead
        exact hhead.symm ▸ hfEnds.2
      have hYExposed : Y ∈
          GroundingSimultaneousDecode.exposedLadderPaths
            (EqualInput L hL) p.1 := by
        apply (EqualInput L hL).mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
          (L.popularAuxiliary_proxyPathsFaithful hL) p.1
          ((ActiveWarp hL M).starts_in_source p.2) hY hvCarrier
          (Y.edgeSet_subset_support_prod huvY).2
      exact ⟨Y, hY, hYExposed, u,
        (Y.edgeSet_subset_support_prod huvY).1,
        R.path.start, haSource, hauE⟩

/-- Final target-only compiler for the concrete maximal ordered active
relation.  Every structural obligation is automatic; it remains only to
root the selected minimal target boundary in this one explicit relation. -/
theorem ReservedGroundedParent.exists_hindrance_of_maximalOrderedActive_targetRooted
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {q : FinitePath (EqualInput L hL).lambda.graph}
    {hqsource : q.start ∈ (EqualInput L hL).lambda.source}
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    (T : L.MinimalReachableTargetBoundary hL)
    (hroot : ∀ b ∈ T.vertices,
      ∃ a ∈ Gamma.source,
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ canonicalErasedRepairedEdges
            (EqualInput L hL) (ActiveWarp hL M)) a b) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  let E := canonicalErasedRepairedEdges (EqualInput L hL) (ActiveWarp hL M)
  let A : Set V := Gamma.source \ {R.parent.initial}
  apply
    GroundingRootedReachabilityHindrance.exists_hindrance_of_rootedSeparatingAntichain
      E A T.vertices (unused := R.parent.initial)
  · exact canonicalErasedRepairedEdges_subset_adj
      (EqualInput L hL) (ActiveWarp hL M)
  · exact canonicalErasedRepairedEdges_biUnique
      (EqualInput L hL) (ActiveWarp hL M)
      (maximalOrderedActiveSubwarp_decodedCarriers_pairwiseDisjoint M)
  · exact Set.sdiff_subset
  · intro b hb c _hc hbc
    rcases hbc.cases_head with hcb | ⟨x, hbx, _hxc⟩
    · exact hcb
    · exact False.elim
        (terminalCut_noOutgoing_canonicalErasedRepairedEdges
          L hL (ActiveWarp hL M) (T.subset_reachableTerminalCut hb).1
          ⟨x, hbx⟩)
  · intro b hb
    obtain ⟨a, ha, hab⟩ := hroot b hb
    have havoid : ∀ p ∈ (ActiveWarp hL M).paths,
        Disjoint p.support (collisionCarrier (EqualInput L hL) q) := by
      intro p hp
      exact M.paths_avoid hp.1
    have hane : a ≠ R.parent.initial := by
      intro hae
      subst a
      exact R.not_reaches_terminalCut (ActiveWarp hL M) havoid
        (T.subset_reachableTerminalCut hb).1 hab
    exact ⟨a, ⟨ha, by simpa using hane⟩, hab⟩
  · exact T.separates
  · exact R.parent_initial_source
  · simp [A]

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.maximalActive_routesThroughIndex_repairedEdges_biUnique
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_mem_current_backward_or_forwardConflict_of_mem_before_not_mem_through
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_routeInitial_rooted_through_or_currentDeletion
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_exists_sourceRooted_routeVertex_or_exposedParentPoint_through
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_rootParentEdge_currentDeletion_of_not_mem_full
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_otherRoute_decodedCarrier_disjoint_exposedParent
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_otherRoute_decodedCarrier_disjoint_backwardOwner
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_exposedParentEdge_currentDeletion_of_not_mem_full
#print axioms Erdos599.DWeb.KappaLadder.maximalActive_exists_sourceRooted_routeVertex_or_exposedParentPoint_full
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.exists_hindrance_of_maximalOrderedActive_targetRooted
