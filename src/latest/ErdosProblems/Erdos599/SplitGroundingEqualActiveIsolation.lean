/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingEqualMaximalOrdered
import ErdosProblems.Erdos599.GroundingErasedCarrierRank

/-!
# Isolation of grounded parents in the split ordered active family

If an active route exposes and meets one limiting-ladder component, every
other active decoded carrier avoids that component.  Later routes avoid it
directly; an earlier contact would expose it to the earlier route and force
the later route to avoid its own contact.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace DWeb.KappaLadder

open GroundingEqualActiveSelection
open GroundingEqualOrderedActiveSelection
open GroundingSimultaneousDecode

variable {kappa : Cardinal.{u}}

private abbrev SplitIsolationInput
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance) :=
  L.splitPopularAuxiliaryInput hL.legal

/-- An exposed component actually met by one active route is isolated from
every other active decoded carrier. -/
theorem splitMaximalActive_otherRoute_decodedCarrier_disjoint_exposedParent
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {reserved : FinitePath (SplitIsolationInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitIsolationInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitIsolationInput L hL) reserved)}
    (p r : WarpPath (splitMaximalOrderedActiveSubwarp hL M))
    (hrp : r ≠ p)
    {Y : Gamma.DPath}
    (hY : Y ∈ exposedLadderPaths (SplitIsolationInput L hL) p.1)
    (hself : ((SplitIsolationInput L hL).decodedVertexCarrier p.1 ∩
      Y.support).Nonempty) :
    Disjoint ((SplitIsolationInput L hL).decodedVertexCarrier r.1)
      Y.support := by
  let I := SplitIsolationInput L hL
  let U := L.splitPopularAuxiliaryIndexed hL
  let W := splitMaximalOrderedActiveSubwarp hL M
  have hindexNe :
      warpPathIndex U W r ≠ warpPathIndex U W p := by
    intro heq
    exact hrp (warpPath_eq_of_index_eq U
      (L.splitPopularAuxiliaryIndexed_sourceIndexed hL) W heq)
  rcases lt_or_gt_of_ne hindexNe with hrlt | hplt
  · rw [Set.disjoint_left]
    intro x hxr hxY
    have hYLadder : Y ∈ I.ladder.paths :=
      GroundingErasedCarrierRank.exposedLadderPaths_subset_ladder
        (L.splitPopularAuxiliary_proxyPathsFaithful hL) p.1 hY
    have hYExposedR : Y ∈ exposedLadderPaths I r.1 := by
      apply I.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
        (L.splitPopularAuxiliary_proxyPathsFaithful hL) r.1
        (W.starts_in_source r.2) hYLadder hxr hxY
    have hpAvoidSupport :=
      splitMaximalOrderedActiveSubwarp_orderedAvoidance M p.2 r.2 hrlt
    have hpAvoid : Disjoint (I.decodedVertexCarrier p.1) Y.support :=
      decodedVertexCarrier_disjoint_exposedLadderPath_of_support_disjoint
        I (L.splitPopularAuxiliary_proxyPathsFaithful hL)
        p.1 r.1 (W.starts_in_source p.2) hYExposedR hpAvoidSupport
    obtain ⟨z, hzp, hzY⟩ := hself
    exact Set.disjoint_left.1 hpAvoid hzp hzY
  · have hrAvoidSupport :=
      splitMaximalOrderedActiveSubwarp_orderedAvoidance M r.2 p.2 hplt
    exact
      decodedVertexCarrier_disjoint_exposedLadderPath_of_support_disjoint
        I (L.splitPopularAuxiliary_proxyPathsFaithful hL)
        r.1 p.1 (W.starts_in_source r.2) hY hrAvoidSupport

/-- In particular, every other active route avoids a grounded route's
represented root parent. -/
theorem splitMaximalActive_otherRoute_disjoint_rootParent
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {reserved : FinitePath (SplitIsolationInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitIsolationInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitIsolationInput L hL) reserved)}
    (p r : WarpPath (splitMaximalOrderedActiveSubwarp hL M))
    (hrp : r ≠ p)
    (R : L.SplitCanonicalErasedRouteRootPrefix hL
      (splitMaximalOrderedActiveSubwarp hL M) p) :
    Disjoint ((SplitIsolationInput L hL).decodedVertexCarrier r.1)
      R.parentData.parent.support := by
  let I := SplitIsolationInput L hL
  let W := splitMaximalOrderedActiveSubwarp hL M
  have hinitialParent :
      (canonicalErasedRoute I W p).initial ∈
        R.parentData.parent.support := by
    rw [← R.finish_eq]
    exact R.support_subset R.path.finish_mem_support
  have hinitialCarrier :
      (canonicalErasedRoute I W p).initial ∈
        I.decodedVertexCarrier p.1 :=
    canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier I W p
      (canonicalErasedRoute I W p).initial_mem_vertexSet
  exact splitMaximalActive_otherRoute_decodedCarrier_disjoint_exposedParent
    p r hrp R.parentData.parent_exposed
      ⟨_, hinitialCarrier, hinitialParent⟩

/-- A root-parent edge deleted by the full active relation is deleted by
the route which owns that parent, never by another active route. -/
theorem splitMaximalActive_rootParentEdge_currentDeletion_of_not_mem
    {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
    {reserved : FinitePath (SplitIsolationInput L hL).lambda.graph}
    {M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (SplitIsolationInput L hL)
      (L.splitGroundedAuxiliarySources hL \ {reserved.start})
      (collisionCarrier (SplitIsolationInput L hL) reserved)}
    (p : WarpPath (splitMaximalOrderedActiveSubwarp hL M))
    (R : L.SplitCanonicalErasedRouteRootPrefix hL
      (splitMaximalOrderedActiveSubwarp hL M) p)
    {e : V × V} (heParent : e ∈ R.parentData.parent.edgeSet)
    (heNot : e ∉ canonicalErasedRepairedEdges
      (SplitIsolationInput L hL)
      (splitMaximalOrderedActiveSubwarp hL M)) :
    e ∈ (canonicalErasedRoute
        (SplitIsolationInput L hL)
        (splitMaximalOrderedActiveSubwarp hL M) p).directionEdges .backward ∨
      ∃ f ∈ (canonicalErasedRoute
          (SplitIsolationInput L hL)
          (splitMaximalOrderedActiveSubwarp hL M) p).directionEdges .forward,
        e.1 = f.1 ∨ e.2 = f.2 := by
  let I := SplitIsolationInput L hL
  let W := splitMaximalOrderedActiveSubwarp hL M
  have heFamily : e ∈ I.familyEdges :=
    ⟨R.parentData.parent, R.parentData.parent_inessential.1, heParent⟩
  by_cases heBackward : e ∈ canonicalErasedBackwardEdges I W
  · simp only [canonicalErasedBackwardEdges, Set.mem_iUnion] at heBackward
    obtain ⟨r, her⟩ := heBackward
    have hrp : r = p := by
      by_contra hne
      have hdisj :=
        splitMaximalActive_otherRoute_disjoint_rootParent p r hne R
      have hends := AltPath.directionEdge_endpoints_mem_vertexSet
        (canonicalErasedRoute I W r) her
      have hcarrier :=
        canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
          I W r hends.1
      exact Set.disjoint_left.1 hdisj hcarrier
        (R.parentData.parent.edgeSet_subset_support_prod heParent).1
    left
    subst r
    exact her
  · have heResidual : e ∈ canonicalErasedResidualEdges I W :=
      ⟨heFamily, heBackward⟩
    have heConflict : e ∈ canonicalErasedForwardConflictEdges I W := by
      by_contra heNotConflict
      exact heNot (Or.inl ⟨heResidual, heNotConflict⟩)
    obtain ⟨f, hf, htail | hhead⟩ := heConflict
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      have hrp : r = p := by
        by_contra hne
        have hdisj :=
          splitMaximalActive_otherRoute_disjoint_rootParent p r hne R
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute I W r) hfr
        have hcarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
            I W r hends.1
        exact Set.disjoint_left.1 hdisj hcarrier
          (htail ▸
            (R.parentData.parent.edgeSet_subset_support_prod heParent).1)
      right
      subst r
      exact ⟨f, hfr, Or.inl htail⟩
    · simp only [canonicalErasedForwardEdges, Set.mem_iUnion] at hf
      obtain ⟨r, hfr⟩ := hf
      have hrp : r = p := by
        by_contra hne
        have hdisj :=
          splitMaximalActive_otherRoute_disjoint_rootParent p r hne R
        have hends := AltPath.directionEdge_endpoints_mem_vertexSet
          (canonicalErasedRoute I W r) hfr
        have hcarrier :=
          canonicalErasedRoute_vertexSet_subset_decodedVertexCarrier
            I W r hends.2
        exact Set.disjoint_left.1 hdisj hcarrier
          (hhead ▸
            (R.parentData.parent.edgeSet_subset_support_prod heParent).2)
      right
      subst r
      exact ⟨f, hfr, Or.inr hhead⟩

end DWeb.KappaLadder
end Erdos599
