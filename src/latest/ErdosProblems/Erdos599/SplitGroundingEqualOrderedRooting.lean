/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualTargetContact

/-!
# Ordered source roots for strict-free split equal routes

Before one route is inserted, every lower-index decoded carrier avoids both
its grounded source parent and every grounded backward owner.  Therefore
finite prefixes in those parents survive the repaired relation of the lower
initial segment.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating Stationary

universe u

variable {V : Type u} {Gamma : DWeb V}

private theorem splitAltPath_link_support_subset_vertexSet
    {Q : AltPath Gamma.graph} {l : Link Gamma.graph}
    (hl : l ∈ Q.links) :
    l.path.support ⊆ Q.vertexSet := by
  cases Q with
  | trivial v => simp at hl
  | finite Q =>
      simp only [AltPath.links, FiniteTrace.links, Set.mem_range] at hl
      obtain ⟨i, rfl⟩ := hl
      intro x hx
      exact Set.mem_iUnion.2 ⟨i, hx⟩
  | infinite Q =>
      simp only [AltPath.links, InfiniteTrace.links, Set.mem_range] at hl
      obtain ⟨i, rfl⟩ := hl
      intro x hx
      exact Set.mem_iUnion.2 ⟨i, hx⟩

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingSimultaneousDecode

variable {kappa : Cardinal.{u}}

private abbrev SplitOrderedRootInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

namespace SplitReservedStationaryEqualSelection

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {P : Popular.XSWarp
    (SplitOrderedRootInput L hL).lambda
    (SplitOrderedRootInput L hL).lambda.target}

/-- Ordered collision-carrier avoidance descends to strict routes. -/
theorem strictRoutes_orderedAvoidance
    (S : L.SplitReservedStationaryEqualSelection hL P)
    {p q : FinitePath (SplitOrderedRootInput L hL).lambda.graph}
    (hp : p ∈ S.strictRoutes.paths) (hq : q ∈ S.strictRoutes.paths)
    (hqp : (L.splitPopularAuxiliaryIndexed hL).f
        ⟨q.start, S.strictRoutes.starts_in_source hq⟩ <
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.start, S.strictRoutes.starts_in_source hp⟩) :
    Disjoint p.support
      (GroundingEqualActiveSelection.collisionCarrier
        (SplitOrderedRootInput L hL) q) := by
  have hpRoutes := S.strictRoutes_subset_routes hp
  have hqRoutes := S.strictRoutes_subset_routes hq
  apply S.routes_orderedAvoidance hpRoutes hqRoutes
  simpa only [] using hqp

/-- A later strict route's decoded carrier avoids each limiting component
exposed by an earlier strict route. -/
theorem strictRoutes_later_decodedCarrier_disjoint_earlier_exposed
    (S : L.SplitReservedStationaryEqualSelection hL P)
    {p q : FinitePath (SplitOrderedRootInput L hL).lambda.graph}
    (hp : p ∈ S.strictRoutes.paths) (hq : q ∈ S.strictRoutes.paths)
    (hqp : (L.splitPopularAuxiliaryIndexed hL).f
        ⟨q.start, S.strictRoutes.starts_in_source hq⟩ <
      (L.splitPopularAuxiliaryIndexed hL).f
        ⟨p.start, S.strictRoutes.starts_in_source hp⟩)
    {Y : Gamma.DPath}
    (hY : Y ∈ exposedLadderPaths (SplitOrderedRootInput L hL) q) :
    Disjoint
      ((SplitOrderedRootInput L hL).decodedVertexCarrier p)
      Y.support := by
  apply decodedVertexCarrier_disjoint_exposedLadderPath_of_support_disjoint
    (SplitOrderedRootInput L hL)
    (L.splitPopularAuxiliary_proxyPathsFaithful hL) p q
    (S.strictRoutes.starts_in_source hp) hY
  exact S.strictRoutes_orderedAvoidance hp hq hqp

/-- Every strict route has its finite original-source prefix. -/
theorem strictRoute_has_rootPrefix
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (q : WarpPath S.strictRoutes) :
    Nonempty (L.SplitCanonicalErasedRouteRootPrefix hL S.strictRoutes q) :=
  L.exists_splitCanonicalErasedRouteRootPrefix hL S.strictRoutes q
    (S.strictRoutes_ground q.1 q.2)

/-- A lower-index route cannot meet the grounded root parent of a later
route. -/
theorem earlierStrictRoute_decodedCarrier_disjoint_rootParent
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (r q : WarpPath S.strictRoutes)
    (hrq : warpPathIndex (L.splitPopularAuxiliaryIndexed hL) S.strictRoutes r <
      warpPathIndex (L.splitPopularAuxiliaryIndexed hL) S.strictRoutes q)
    (R : L.SplitCanonicalErasedRouteRootPrefix hL S.strictRoutes q) :
    Disjoint
      ((SplitOrderedRootInput L hL).decodedVertexCarrier r.1)
      R.parentData.parent.support := by
  let J := SplitOrderedRootInput L hL
  rw [Set.disjoint_left]
  intro x hxr hxparent
  have hparentExposed : R.parentData.parent ∈
      exposedLadderPaths J r.1 := by
    apply J.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
      (L.splitPopularAuxiliary_proxyPathsFaithful hL) r.1
      (S.strictRoutes.starts_in_source r.2)
      R.parentData.parent_inessential.1 hxr hxparent
  have havoid :=
    S.strictRoutes_later_decodedCarrier_disjoint_earlier_exposed
      q.2 r.2 hrq hparentExposed
  let y := (canonicalErasedRoute J S.strictRoutes q).initial
  have hyq : y ∈ J.decodedVertexCarrier q.1 :=
    canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
      J S.strictRoutes q
      (canonicalErasedRoute J S.strictRoutes q).initial_mem_vertexSet
  have hyparent : y ∈ R.parentData.parent.support := by
    have hfinish : R.path.finish = y := by
      simpa only [y, J] using R.finish_eq
    rw [← hfinish]
    exact R.support_subset R.path.finish_mem_support
  exact Set.disjoint_left.1 havoid hyq hyparent

/-- Strict routes below one source index. -/
def strictRoutesBeforeIndex
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (a : Below kappa) :
    Popular.XSWarp
      (SplitOrderedRootInput L hL).lambda
      (SplitOrderedRootInput L hL).lambda.target where
  paths := {p | ∃ hp : p ∈ S.strictRoutes.paths,
    warpPathIndex (L.splitPopularAuxiliaryIndexed hL) S.strictRoutes
      ⟨p, hp⟩ < a}
  disjoint := by
    rintro p ⟨hp, _⟩ q ⟨hq, _⟩ hpq
    exact S.strictRoutes.disjoint hp hq hpq
  starts_in_source := by
    rintro p ⟨hp, _⟩
    exact S.strictRoutes.starts_in_source hp
  ends_in_target := by
    rintro p ⟨hp, _⟩
    exact S.strictRoutes.ends_in_target hp

theorem strictRoutesBeforeIndex_paths_subset
    (S : L.SplitReservedStationaryEqualSelection hL P) (a : Below kappa) :
    (S.strictRoutesBeforeIndex a).paths ⊆ S.strictRoutes.paths := by
  rintro p ⟨hp, _⟩
  exact hp

theorem strictRoutesBeforeIndex_decodedDisjoint
    (S : L.SplitReservedStationaryEqualSelection hL P) (a : Below kappa) :
    (S.strictRoutesBeforeIndex a).paths.PairwiseDisjoint
      (SplitOrderedRootInput L hL).decodedVertexCarrier := by
  intro p hp q hq hpq
  exact S.strictRoutes_decodedCarriers_pairwiseDisjoint
    (S.strictRoutesBeforeIndex_paths_subset a hp)
    (S.strictRoutesBeforeIndex_paths_subset a hq) hpq

theorem strictRoutesBeforeIndex_repaired_subset_adj
    (S : L.SplitReservedStationaryEqualSelection hL P) (a : Below kappa) :
    canonicalErasedRepairedEdges (SplitOrderedRootInput L hL)
      (S.strictRoutesBeforeIndex a) ⊆ {e | Gamma.graph.Adj e.1 e.2} :=
  canonicalErasedRepairedEdges_subset_adj
    (SplitOrderedRootInput L hL) (S.strictRoutesBeforeIndex a)

/-- A finite prefix in a ladder component avoided by all lower routes
survives their repaired relation. -/
theorem finiteParentPrefix_survives_strictRoutesBeforeIndex
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (a : Below kappa) (parent : Gamma.DPath)
    (hparent : parent ∈ (SplitOrderedRootInput L hL).ladder.paths)
    (r : FinitePath Gamma.graph) (hr : r.edgeSet ⊆ parent.edgeSet)
    (havoid : ∀ q : WarpPath (S.strictRoutesBeforeIndex a),
      Disjoint
        ((SplitOrderedRootInput L hL).decodedVertexCarrier q.1)
        parent.support) :
    r.edgeSet ⊆ canonicalErasedRepairedEdges
      (SplitOrderedRootInput L hL) (S.strictRoutesBeforeIndex a) := by
  let J := SplitOrderedRootInput L hL
  let W := S.strictRoutesBeforeIndex a
  intro e he
  have heParent : e ∈ parent.edgeSet := hr he
  have heFamily : e ∈ J.familyEdges := ⟨parent, hparent, heParent⟩
  by_cases heRepaired : e ∈ canonicalErasedRepairedEdges J W
  · exact heRepaired
  by_cases heBackward : e ∈ canonicalErasedBackwardEdges J W
  · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackward
    obtain ⟨q, hqe⟩ := heBackward
    have hends := AltPath.directionEdge_endpoints_mem_vertexSet
      (canonicalErasedRoute J W q) hqe
    have hcarrier :=
      canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J W q
    exact False.elim <| Set.disjoint_left.1 (havoid q) (hcarrier hends.1)
      (parent.edgeSet_subset_support_prod heParent).1
  · have heResidual : e ∈ canonicalErasedResidualEdges J W :=
      ⟨heFamily, heBackward⟩
    have heConflict : e ∈ canonicalErasedForwardConflictEdges J W := by
      by_contra heNotConflict
      exact heRepaired (Or.inl ⟨heResidual, heNotConflict⟩)
    obtain ⟨f, hfForward, htail | hhead⟩ := heConflict
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
      obtain ⟨q, hqf⟩ := hfForward
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute J W q) hqf
      have hcarrier :=
        canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J W q
      exact False.elim <| Set.disjoint_left.1 (havoid q)
        (htail.symm ▸ hcarrier hends.1)
        (parent.edgeSet_subset_support_prod heParent).1
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hfForward
      obtain ⟨q, hqf⟩ := hfForward
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute J W q) hqf
      have hcarrier :=
        canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier J W q
      exact False.elim <| Set.disjoint_left.1 (havoid q)
        (hhead.symm ▸ hcarrier hends.2)
        (parent.edgeSet_subset_support_prod heParent).2

/-- Immediately before a strict route is inserted, its erased initial is
rooted in the original source. -/
theorem strictRoute_initial_sourceRooted_beforeIndex
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (q : WarpPath S.strictRoutes)
    (R : L.SplitCanonicalErasedRouteRootPrefix hL S.strictRoutes q) :
    ∃ x ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ canonicalErasedRepairedEdges
          (SplitOrderedRootInput L hL)
          (S.strictRoutesBeforeIndex
            (warpPathIndex (L.splitPopularAuxiliaryIndexed hL)
              S.strictRoutes q)))
        x (canonicalErasedRoute
          (SplitOrderedRootInput L hL) S.strictRoutes q).initial := by
  let a := warpPathIndex (L.splitPopularAuxiliaryIndexed hL) S.strictRoutes q
  have havoid : ∀ r : WarpPath (S.strictRoutesBeforeIndex a),
      Disjoint
        ((SplitOrderedRootInput L hL).decodedVertexCarrier r.1)
        R.parentData.parent.support := by
    intro r
    obtain ⟨hr, hrlt⟩ := r.2
    exact S.earlierStrictRoute_decodedCarrier_disjoint_rootParent
      ⟨r.1, hr⟩ q hrlt R
  have hsurvive :=
    S.finiteParentPrefix_survives_strictRoutesBeforeIndex a
      R.parentData.parent R.parentData.parent_inessential.1
      R.path R.edgeSet_subset havoid
  exact R.reaches_initial hsurvive

/-- A grounded backward owner start is rooted before the current strict
route is inserted. -/
theorem strictBackwardOwner_start_sourceRooted_beforeIndex
    (S : L.SplitReservedStationaryEqualSelection hL P)
    (q : WarpPath S.strictRoutes)
    (l : Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (SplitOrderedRootInput L hL)
      ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp S.routes)
      ⟨q.1, S.strictRoutes_subset_equalRoutes q.2⟩).links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath)
    (hparent : parent ∈ (SplitOrderedRootInput L hL).ladder.paths)
    (hparentSource : parent.initial ∈ Gamma.source)
    (hsub : l.path.IsSubpathOf parent) :
    ∃ x ∈ Gamma.source,
      Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈ canonicalErasedRepairedEdges
          (SplitOrderedRootInput L hL)
          (S.strictRoutesBeforeIndex
            (warpPathIndex (L.splitPopularAuxiliaryIndexed hL)
              S.strictRoutes q)))
        x l.path.start := by
  let a := warpPathIndex (L.splitPopularAuxiliaryIndexed hL) S.strictRoutes q
  obtain ⟨r, hrStart, hrFinish, _hrSupport, hrEdges⟩ :=
    GroundingPathPrefix.exists_initialFinitePrefix parent
      (hsub.1 l.path.start_mem_support)
  have havoid : ∀ p : WarpPath (S.strictRoutesBeforeIndex a),
      Disjoint
        ((SplitOrderedRootInput L hL).decodedVertexCarrier p.1)
        parent.support := by
    intro p
    obtain ⟨hpRoutes, hpIndex⟩ := p.2
    rw [Set.disjoint_left]
    intro x hxp hxparent
    have hparentExposed : parent ∈
        exposedLadderPaths (SplitOrderedRootInput L hL) p.1 := by
      apply (SplitOrderedRootInput L hL)
        |>.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
          (L.splitPopularAuxiliary_proxyPathsFaithful hL) p.1
          ((S.strictRoutesBeforeIndex a).starts_in_source p.2)
          hparent hxp hxparent
    have hdisj :=
      S.strictRoutes_later_decodedCarrier_disjoint_earlier_exposed
        q.2 hpRoutes hpIndex hparentExposed
    have hqLink :
        l.path.start ∈
          (SplitOrderedRootInput L hL).decodedVertexCarrier q.1 := by
      apply canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
        (SplitOrderedRootInput L hL)
        ((L.splitPopularAuxiliaryIndexed hL).equalSubwarp S.routes)
        ⟨q.1, S.strictRoutes_subset_equalRoutes q.2⟩
      exact splitAltPath_link_support_subset_vertexSet hl
        l.path.start_mem_support
    exact Set.disjoint_left.1 hdisj hqLink
      (hsub.1 l.path.start_mem_support)
  have hrSurvives :=
    S.finiteParentPrefix_survives_strictRoutesBeforeIndex
      a parent hparent r hrEdges havoid
  refine ⟨r.start, ?_, ?_⟩
  · simpa only [hrStart] using hparentSource
  · simpa only [hrFinish] using
      (GroundingRootedReachabilityWarp.finitePath_start_reaches_of_mem_support
        r hrSurvives r.finish_mem_support)

end SplitReservedStationaryEqualSelection
end DWeb.KappaLadder
end Erdos599
