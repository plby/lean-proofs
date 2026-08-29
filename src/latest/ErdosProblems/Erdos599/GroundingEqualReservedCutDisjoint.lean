/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingEqualMaximalActiveSupply
import ErdosProblems.Erdos599.GroundingErasedCarrierRank
import ErdosProblems.Erdos599.GroundingEqualCollisionBoundaryOwners
import ErdosProblems.Erdos599.GroundingFragmentRelation
import ErdosProblems.Erdos599.GroundingFragmentWarp
import ErdosProblems.Erdos599.GroundingFragmentUniqueness
import ErdosProblems.Erdos599.GroundingCutDecoder
import ErdosProblems.Erdos599.GroundingSelectedForwardOrder
import ErdosProblems.Erdos599.SafeSwitching
import ErdosProblems.Erdos599.LadderSuccessorBridge

/-!
# The corrected equal-stage boundary avoids the reserved parent

The reserved auxiliary route itself is not part of the corrected collision
cut.  This file records the corresponding original-web disjointness facts.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath
open GroundingEqualActiveSelection GroundingSimultaneousDecode
open _root_.Erdos599.GroundingErasedCarrierRank

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
  {q : FinitePath (EqualInput L hL).lambda.graph}
  {hqsource : q.start ∈ (EqualInput L hL).lambda.source}

namespace ReservedGroundedParent

/-- A target marker belongs to an essential limiting-ladder path, whereas
the reserved parent is inessential.  Hence they cannot meet. -/
theorem targetMarkers_disjoint
    (R : L.ReservedGroundedParent hL q hqsource) :
    Disjoint R.parent.support (EqualInput L hL).targetMarkers := by
  rw [Set.disjoint_left]
  intro b hbR hbTarget
  obtain ⟨Y, hYessential, hbY⟩ := hbTarget.2
  exact (Gamma.not_mem_inessentialPaths_of_intersects_essential
    (hL.legal.warpStages (Ladder.finalStage kappa)) hYessential
    ⟨b, hbR, hbY⟩) R.parent_inessential

/-- A route avoiding the reserved collision carrier cannot expose the
reserved limiting-ladder component.  In the ordinary case an actual route
vertex witnesses the collision; in the initial-proxy case the proxy gadget
itself witnesses it. -/
theorem exposedLadderPath_ne_parent
    (R : L.ReservedGroundedParent hL q hqsource)
    {r : FinitePath (EqualInput L hL).lambda.graph}
    (havoid : Disjoint r.support (collisionCarrier (EqualInput L hL) q))
    {Y : Gamma.DPath}
    (hY : Y ∈ exposedLadderPaths (EqualInput L hL) r) :
    Y ≠ R.parent := by
  intro hEq
  subst Y
  rcases hY with hmet | hproxy
  · obtain ⟨a, har, haTrace⟩ := hmet.2
    exact Set.disjoint_left.1 havoid har (Or.inl (Or.inr
      ((mem_metLadderTrace_iff (EqualInput L hL) q a).2
        ⟨R.parent, R.parent_exposed, haTrace⟩)))
  · cases hrs : r.start with
    | old b => simp [hrs] at hproxy
    | edge a b => simp [hrs] at hproxy
    | proxy i =>
        have hParentProxy : R.parent = (EqualInput L hL).proxyPath i := by
          simpa [exposedLadderPaths, hrs] using hproxy
        apply Set.disjoint_left.1 havoid r.start_mem_support
        rw [hrs]
        exact Or.inr ⟨i, rfl, by
          simpa only [← hParentProxy] using R.parent_exposed⟩

/-- Consequently every limiting-ladder component exposed by an avoiding
route is support-disjoint from the reserved parent. -/
theorem exposedLadderPath_support_disjoint_parent
    (R : L.ReservedGroundedParent hL q hqsource)
    {r : FinitePath (EqualInput L hL).lambda.graph}
    (havoid : Disjoint r.support (collisionCarrier (EqualInput L hL) q))
    {Y : Gamma.DPath}
    (hY : Y ∈ exposedLadderPaths (EqualInput L hL) r) :
    Disjoint Y.support R.parent.support := by
  have hYL : Y ∈ L.limitWarp :=
    exposedLadderPaths_subset_ladder
      (L.popularAuxiliary_proxyPathsFaithful hL) r hY
  exact (hL.legal.warpStages (Ladder.finalStage kappa)) hYL
    R.parent_inessential.1 (R.exposedLadderPath_ne_parent havoid hY)

/-- Old-vertex provenance from an avoiding route cannot name a point of the
reserved parent. -/
theorem oldCollisionProvenance_not_mem_parent
    (R : L.ReservedGroundedParent hL q hqsource)
    {r : FinitePath (EqualInput L hL).lambda.graph}
    (havoid : Disjoint r.support (collisionCarrier (EqualInput L hL) q))
    (hdecoded : Disjoint ((EqualInput L hL).decodedVertexCarrier r)
      R.parent.support)
    {b : V} (hb : OldCollisionProvenance (EqualInput L hL) r b) :
    b ∉ R.parent.support := by
  intro hbR
  rcases hb with hbDirect | ⟨Y, hYr, hbY⟩
  · exact Set.disjoint_left.1 hdecoded hbDirect.2 hbR
  · exact Set.disjoint_left.1
      (R.exposedLadderPath_support_disjoint_parent havoid hYr) hbY hbR

/-- Both original endpoints named by edge provenance from an avoiding route
lie off the reserved parent. -/
theorem edgeCollisionProvenance_endpoints_not_mem_parent
    (R : L.ReservedGroundedParent hL q hqsource)
    {r : FinitePath (EqualInput L hL).lambda.graph}
    (havoid : Disjoint r.support (collisionCarrier (EqualInput L hL) q))
    (hdecoded : Disjoint ((EqualInput L hL).decodedVertexCarrier r)
      R.parent.support)
    {u v : V} (he : EdgeCollisionProvenance (EqualInput L hL) r u v) :
    u ∉ R.parent.support ∧ v ∉ R.parent.support := by
  rcases he with heDirect | ⟨Y, hYr, huvY⟩
  · exact ⟨fun huR ↦ Set.disjoint_left.1 hdecoded heDirect.2.1 huR,
      fun hvR ↦ Set.disjoint_left.1 hdecoded heDirect.2.2 hvR⟩
  · have hdisj := R.exposedLadderPath_support_disjoint_parent havoid hYr
    have huvSupport := Y.edgeSet_subset_support_prod huvY
    exact ⟨fun huR ↦ Set.disjoint_left.1 hdisj huvSupport.1 huR,
      fun hvR ↦ Set.disjoint_left.1 hdisj huvSupport.2 hvR⟩

/-- The old-vertex part of the corrected target-plus-selected cut is
disjoint from the reserved inessential parent. -/
theorem CV_targetCollisionCut_disjoint_parent
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    Disjoint
      (GroundingCut.CV (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths))
      R.parent.support := by
  rw [Set.disjoint_left]
  intro b hbCV hbR
  rcases (mem_CV_reservedMaximalTargetCollisionCut_iff
      (EqualInput L hL) M.paths b).1 hbCV with hbTarget | ⟨r, hrM, hprov⟩
  · exact Set.disjoint_left.1 R.targetMarkers_disjoint hbR hbTarget
  · apply R.oldCollisionProvenance_not_mem_parent
      (M.paths_avoid hrM)
      (ReservedMaximalDecodedActiveSupply.decodedCarriers_disjoint_reservedParent
        R M r hrM) hprov hbR

/-- Every represented original edge in the corrected cut has both endpoints
off the reserved parent.  In particular no edge of the parent is deleted. -/
theorem CE_targetCollisionCut_endpoints_not_mem_parent
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {u v : V}
    (huv : (u, v) ∈ GroundingCut.CE (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)) :
    u ∉ R.parent.support ∧ v ∉ R.parent.support := by
  obtain ⟨huvCut, _huvFamily⟩ := huv
  obtain ⟨r, hrM, hprov⟩ :=
    (edge_mem_reservedMaximalTargetCollisionCut_iff
      (EqualInput L hL) M.paths u v).1 huvCut
  exact R.edgeCollisionProvenance_endpoints_not_mem_parent
    (M.paths_avoid hrM)
    (ReservedMaximalDecodedActiveSupply.decodedCarriers_disjoint_reservedParent
      R M r hrM) hprov

/-- In the infinite-record case, the auxiliary proxy naming the reserved
parent is absent from the corrected target-plus-selected collision cut. -/
theorem sourceProxy_not_mem_targetCollisionCut
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {i : L.groundedInfiniteRecords}
    (hparent : R.parent = (EqualInput L hL).proxyPath i)
    (hstart : q.start = .proxy i) :
    (PopularAuxiliary.Input.LambdaVertex.proxy i :
      (EqualInput L hL).LV) ∉
      reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths := by
  let J := EqualInput L hL
  intro hiCut
  rcases hiCut with hiTarget | hiHull
  · exact J.not_mem_lambda_target_proxy i hiTarget
  · obtain ⟨r, hrM, hir⟩ := (mem_collisionHull).1 hiHull
    rcases hir with (hirSupport | hirTrace) | hirProxy
    · apply Set.disjoint_left.1 (M.paths_avoid hrM) hirSupport
      simpa only [hstart] using
        (show q.start ∈ collisionCarrier J q from
          Or.inl (Or.inl q.start_mem_support))
    · obtain ⟨Y, _hYr, hiY⟩ :=
        (mem_metLadderTrace_iff J r (.proxy i)).1 hirTrace
      rcases hiY with ⟨x, _hxY, hxi⟩ | ⟨e, _heY, hei⟩
      · cases hxi
      · cases hei
    · obtain ⟨j, hij, hjr⟩ := hirProxy
      cases hij
      exact (R.exposedLadderPath_ne_parent (M.paths_avoid hrM) hjr)
        hparent.symm

theorem parent_edgeSet_disjoint_CE_targetCollisionCut
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    Disjoint R.parent.edgeSet
      (GroundingCut.CE (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)) := by
  rw [Set.disjoint_left]
  intro e heR heCE
  exact (R.CE_targetCollisionCut_endpoints_not_mem_parent M heCE).1
    (R.parent.edgeSet_subset_support_prod heR).1

/-- If none of a parent's edges is deleted, every two of its vertices are
in the same surviving component. -/
theorem survivingConnected_parent_of_targetCollisionCut
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {x y : V} (hx : x ∈ R.parent.support) (hy : y ∈ R.parent.support) :
    GroundingCut.SurvivingConnected (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)
      R.parent x y := by
  let C := reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths
  have hCE : Disjoint R.parent.edgeSet (GroundingCut.CE (EqualInput L hL) C) :=
    R.parent_edgeSet_disjoint_CE_targetCollisionCut M
  by_cases hxy : x = y
  · subst y
    exact GroundingFragmentRelation.survivingConnected_refl
      (EqualInput L hL) C R.parent hx
  rcases GroundingCut.beforeEq_total hx hy with hbefore | hbefore
  · obtain ⟨p, hpStart, hpFinish, hpEdges⟩ :=
      GroundingCutDecoder.exists_forward_segment_of_before ⟨hbefore, hxy⟩
    refine ⟨p, Or.inl ⟨hpStart, hpFinish⟩, ?_, hpEdges, ?_⟩
    · intro z hz
      by_cases hzFinish : z = p.finish
      · simpa only [hzFinish, hpFinish] using hy
      · obtain ⟨w, hzw⟩ :=
          p.walk.exists_outgoing_edge_of_mem_of_ne_finish hz hzFinish
        exact (R.parent.edgeSet_subset_support_prod (hpEdges hzw)).1
    · exact Disjoint.mono hpEdges Set.Subset.rfl hCE
  · have hyx : y ≠ x := fun h ↦ hxy h.symm
    obtain ⟨p, hpStart, hpFinish, hpEdges⟩ :=
      GroundingCutDecoder.exists_forward_segment_of_before ⟨hbefore, hyx⟩
    refine ⟨p, Or.inr ⟨hpStart, hpFinish⟩, ?_, hpEdges, ?_⟩
    · intro z hz
      by_cases hzFinish : z = p.finish
      · simpa only [hzFinish, hpFinish] using hx
      · obtain ⟨w, hzw⟩ :=
          p.walk.exists_outgoing_edge_of_mem_of_ne_finish hz hzFinish
        exact (R.parent.edgeSet_subset_support_prod (hpEdges hzw)).1
    · exact Disjoint.mono hpEdges Set.Subset.rfl hCE

/-- Thus a deleted fragment whose parent is the reserved record has the
whole support of that record. -/
theorem fragment_support_eq_parent_of_parent_eq
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {F : (EqualInput L hL).Fragment}
    (hF : F ∈ GroundingCut.fragments (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths))
    (hparent : F.parent = R.parent) :
    F.path.support = F.parent.support := by
  apply Set.Subset.antisymm F.support_subset
  intro x hx
  rw [hF.2]
  refine ⟨hx, ?_⟩
  rw [hparent]
  apply R.survivingConnected_parent_of_targetCollisionCut M
  · exact hparent ▸ F.support_subset F.path.initial_mem_support
  · exact hparent ▸ hx

/-- Support equality plus directed subpath containment identifies the
fragment literally with its reserved parent. -/
theorem fragment_path_eq_parent_of_parent_eq
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {F : (EqualInput L hL).Fragment}
    (hF : F ∈ GroundingCut.fragments (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths))
    (hparent : F.parent = R.parent) :
    F.path = F.parent := by
  classical
  have hsupport : F.path.support = F.parent.support :=
    R.fragment_support_eq_parent_of_parent_eq M hF hparent
  have hinitial : F.path.initial = F.parent.initial := by
    have hforward : GroundingCut.BeforeEq F.parent F.parent.initial
        F.path.initial :=
      GroundingFragmentWarp.initial_beforeEq_of_mem
        (F.support_subset F.path.initial_mem_support)
    have hbackPath : GroundingCut.BeforeEq F.path F.path.initial
        F.parent.initial :=
      GroundingFragmentWarp.initial_beforeEq_of_mem
        (hsupport.symm.subset F.parent.initial_mem_support)
    have hback : GroundingCut.BeforeEq F.parent F.path.initial
        F.parent.initial :=
      GroundingFragmentUniqueness.beforeEq_parent F hbackPath
    exact GroundingCutDecoder.beforeEq_antisymm hback hforward
  cases hParent : F.parent with
  | inl p =>
      cases hPath : F.path with
      | inl r =>
          have hsub : r.IsSubpathOf (.inl p : Gamma.DPath) := by
            constructor
            · simpa only [hPath, hParent, Path.support] using F.support_subset
            · simpa only [hPath, hParent, Path.edgeSet] using F.edges_subset
          have hrStart : r.start = p.start := by
            simpa only [hPath, hParent, Path.initial] using hinitial
          have hfinishPath : GroundingCut.BeforeEq F.path p.finish r.finish :=
            GroundingCut.beforeEq_terminal (by simp [hPath])
              (by
                have hpParent : p.finish ∈ F.parent.support := by
                  simpa only [hParent, Path.support] using p.finish_mem_support
                have hpPath : p.finish ∈ F.path.support :=
                  hsupport.symm.subset hpParent
                simpa only [hPath, Path.support] using hpPath)
          have hfinishParent : GroundingCut.BeforeEq F.parent p.finish r.finish :=
            GroundingFragmentUniqueness.beforeEq_parent F hfinishPath
          have hreverseParent : GroundingCut.BeforeEq F.parent r.finish p.finish :=
            GroundingCut.beforeEq_terminal (by simp [hParent])
              (by
                have hrPath : r.finish ∈ F.path.support := by
                  simpa only [hPath, Path.support] using r.finish_mem_support
                have hrParent : r.finish ∈ F.parent.support :=
                  F.support_subset hrPath
                simpa only [hParent, Path.support] using hrParent)
          have hrFinish : r.finish = p.finish :=
            GroundingCutDecoder.beforeEq_antisymm
              hreverseParent hfinishParent
          have hedge : r.edgeSet = p.edgeSet := by
            rw [Alternating.FinitePath.edgeSet_eq_position_interval p r hsub]
            ext e
            simp only [Set.mem_setOf_eq]
            constructor
            · exact fun he ↦ he.1
            · intro he
              have hep := he
              change e ∈ p.walk.edgeSet at hep
              rw [Alternating.Walk.mem_edgeSet_iff_exists_getVert p.walk] at hep
              rcases hep with ⟨i, hi, hi', heq⟩
              have hstartIdx :
                  p.walk.support.idxOf p.start = 0 := by
                calc
                  p.walk.support.idxOf p.start =
                      p.walk.support.idxOf
                        (p.walk.support[0]'p.support_length_pos) := by
                    rw [p.support_getElem_zero]
                  _ = 0 := by rw [p.isPath.idxOf_getElem]
              have hfinishGet :
                  p.walk.support[p.walk.length]'(by
                    rw [Alternating.Walk.support_length_eq]
                    omega) = p.finish :=
                Alternating.Walk.getElem_length_eq_end p.walk
              have hfinishIdx :
                  p.walk.support.idxOf p.finish = p.walk.length := by
                calc
                  p.walk.support.idxOf p.finish =
                      p.walk.support.idxOf
                        (p.walk.support[p.walk.length]'(by
                          rw [Alternating.Walk.support_length_eq]
                          omega)) := by rw [hfinishGet]
                  _ = p.walk.length := by rw [p.isPath.idxOf_getElem]
              have hiIdx : p.walk.support.idxOf
                  (p.walk.support[i]'(by omega)) = i := by
                rw [p.isPath.idxOf_getElem]
              refine ⟨he, ?_, ?_⟩
              · rw [heq]
                simpa only [hrStart, Prod.fst, hstartIdx, hiIdx] using
                  (Nat.zero_le i)
              · rw [heq]
                simpa only [hrFinish, Prod.fst, hfinishIdx, hiIdx] using hi
          have hrp : r = p :=
            FinitePath.eq_of_start_finish_edgeSet_eq
              r p hrStart hrFinish hedge
          exact congrArg Sum.inl hrp
      | inr r =>
          exfalso
          have hrsub : r.support ⊆ p.support := by
            simpa only [hPath, hParent, Path.support] using F.support_subset
          exact (Set.infinite_range_of_injective r.injective)
            (p.support_finite.subset hrsub)
  | inr p =>
      cases hPath : F.path with
      | inl r =>
          exfalso
          have hpfinite : p.support.Finite := by
            rw [← show r.support = p.support by
              simpa only [hPath, hParent, Path.support] using hsupport]
            exact r.support_finite
          exact (Set.infinite_range_of_injective p.injective) hpfinite
      | inr r =>
          have hrInitial : r.initial = p.initial := by
            simpa only [hPath, hParent, Path.initial] using hinitial
          have hrEdges : r.edgeSet ⊆ p.edgeSet := by
            simpa only [hPath, hParent, Path.edgeSet] using F.edges_subset
          have hedge : r.edgeSet = p.edgeSet := by
            apply Set.Subset.antisymm hrEdges
            rintro e ⟨n, rfl⟩
            have hpn : p n ∈ r.support := by
              rw [show r.support = p.support by
                simpa only [hPath, hParent, Path.support] using hsupport]
              exact p.apply_mem_support n
            obtain ⟨m, hm⟩ := hpn
            have hrEdge : (r m, r (m + 1)) ∈ p.edgeSet :=
              hrEdges ⟨m, rfl⟩
            have hrEdge' : (p n, r (m + 1)) ∈ p.edgeSet := by
              simpa only [hm] using hrEdge
            have hnext : p (n + 1) = r (m + 1) :=
              (Alternating.Path.edgeSet_biUnique (.inr p : Gamma.DPath)).2
                ⟨n, rfl⟩ hrEdge'
            exact ⟨m, Prod.ext hm.symm hnext⟩
          have hrp : r = p :=
            Ray.eq_of_initial_edgeSet_eq r p hrInitial hedge
          exact congrArg Sum.inr hrp

/-- Every fragment of the reserved grounded record is one of the fragments
discarded in `H_empty`.  The finite case is discarded at its terminal,
which lies outside the corrected cut.  In the ray case any escaping point
would, by reverse decoding, give a forbidden cut-avoiding auxiliary path
from the reserved proxy source to the auxiliary target. -/
theorem fragment_mem_HEmpty_of_parent_eq
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {F : (EqualInput L hL).Fragment}
    (hF : F ∈ GroundingCut.fragments (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths))
    (hparent : F.parent = R.parent) :
    F ∈ GroundingCut.HEmpty (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths) := by
  let J := EqualInput L hL
  let C := reservedMaximalTargetCollisionCut J M.paths
  have hwhole : F.path = F.parent :=
    R.fragment_path_eq_parent_of_parent_eq M hF hparent
  refine ⟨hF, hwhole, hparent ▸ R.parent_groundedRecord, ?_⟩
  rcases R.source_represents with
      ⟨p, hparentFinite, _hstartFinite⟩ |
      ⟨i, hparentProxy, hstartProxy⟩
  · left
    refine ⟨p.finish, ?_, ?_⟩
    · simp only [hwhole, hparent, hparentFinite,
        DirectedPath.Path.terminal?_finite]
    · intro hfinishCut
      exact Set.disjoint_left.1 (R.CV_targetCollisionCut_disjoint_parent M)
        hfinishCut (hparentFinite ▸ p.finish_mem_support)
  · right
    obtain ⟨ray, hproxyRay⟩ := J.proxy_isRay i
    have hpathRay : F.path = .inr ray :=
      hwhole.trans (hparent.trans (hparentProxy.trans hproxyRay))
    refine ⟨?_, ?_⟩
    · simpa only [hpathRay] using
        (DirectedPath.Path.not_isFinite_ray ray)
    · intro hmeets
      obtain ⟨b, hbF, ⟨E⟩⟩ := hmeets
      have hbRay : b ∈ DirectedPath.Path.support (.inr ray) := by
        simpa only [hpathRay] using hbF
      obtain ⟨n, hn⟩ :=
        (GroundingCut.mem_support_iff_exists_occursAt
          (.inr ray : Gamma.DPath) b).1 hbRay
      have hstrictRay : GroundingCut.Before (.inr ray : Gamma.DPath)
          b (ray (n + 1)) := by
        refine ⟨⟨n, n + 1, hn, rfl, Nat.le_succ n⟩, ?_⟩
        intro hEq
        have hnb : ray n = b := hn
        have hindices : n = n + 1 := ray.injective (hnb.trans hEq)
        exact Nat.ne_of_lt (Nat.lt_succ_self n) hindices
      have hstrict : GroundingCut.Before F.path b (ray (n + 1)) := by
        simpa only [hpathRay] using hstrictRay
      have hFparentProxy : F.parent = J.proxyPath i :=
        hparent.trans hparentProxy
      have hproxyNotCut :
          (PopularAuxiliary.Input.LambdaVertex.proxy i : J.LV) ∉ C :=
        R.sourceProxy_not_mem_targetCollisionCut M hparentProxy hstartProxy
      obtain ⟨r, hrStart, hrTarget, hrAvoid⟩ :=
        GroundingSelectedForwardOrder.exists_avoiding_proxy_reverse_to_relaxedEscape
          J C F hF hFparentProxy hproxyNotCut hstrict E
      exact PopularAuxiliary.Input.no_avoiding_source_target_path
        J.lambda C (reservedMaximalTargetCollisionCut_isSeparator J M.paths)
        r (hrStart ▸ J.mem_lambda_source_proxy i) hrTarget hrAvoid

/-- Hence no fragment with the reserved parent can survive in `G0`. -/
theorem fragment_not_mem_G0_of_parent_eq
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {F : (EqualInput L hL).Fragment}
    (hparent : F.parent = R.parent) :
    F ∉ GroundingCut.G0 (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths) := by
  rintro ⟨hF, hnotEmpty⟩
  exact hnotEmpty (R.fragment_mem_HEmpty_of_parent_eq M hF hparent)

/-- The complete original-web boundary derived from the corrected cut is
disjoint from the reserved grounded parent.  Its represented old vertices
are disjoint by collision avoidance.  A blocking point on the reserved
parent would belong to a retained fragment with that parent, contradicting
the preceding `H_empty` classification. -/
theorem BB_targetCollisionCut_disjoint_parent
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q)) :
    Disjoint
      (GroundingCut.BB (EqualInput L hL)
        (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths))
      R.parent.support := by
  rw [Set.disjoint_left]
  intro b hbBB hbR
  rcases hbBB with hbCV | hbBL
  · exact Set.disjoint_left.1 (R.CV_targetCollisionCut_disjoint_parent M)
      hbCV hbR
  · obtain ⟨F, hFG0, _hblockable, _hbEq, hbF⟩ :=
      GroundingCut.BL_covered_by_G0 hbBL
    have hparent : F.parent = R.parent :=
      Alternating.DWeb.IsWarp.eq_of_mem_support
        (hL.legal.warpStages (Ladder.finalStage kappa))
        F.parent_mem R.parent_inessential.1
        (F.support_subset hbF) hbR
    exact R.fragment_not_mem_G0_of_parent_eq M hparent hFG0

/-- Owner classification for the corrected boundary, strengthened by the
reserved-record exclusion.  Every blocking owner which survives in `G0`
has a parent different from the reserved grounded record. -/
theorem mem_BB_target_or_selected_or_nonreserved_blockingPoint
    (R : L.ReservedGroundedParent hL q hqsource)
    (M : Popular.MaximalDecodedTargetPureAvoidingRestrictedXSWarp
      (EqualInput L hL)
      ((EqualInput L hL).lambda.source \ {q.start})
      (collisionCarrier (EqualInput L hL) q))
    {b : V}
    (hb : b ∈ GroundingCut.BB (EqualInput L hL)
      (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths)) :
    (b ∈ (EqualInput L hL).targetMarkers ∨
      ∃ r ∈ M.paths, OldCollisionProvenance (EqualInput L hL) r b) ∨
      ∃ F : (EqualInput L hL).Fragment,
        F ∈ GroundingCut.G0 (EqualInput L hL)
          (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths) ∧
        GroundingCut.IsBlockable (EqualInput L hL)
          (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths) F ∧
        GroundingCut.blockingPoint (EqualInput L hL)
          (reservedMaximalTargetCollisionCut (EqualInput L hL) M.paths) F = b ∧
        b ∈ F.path.support ∧ F.parent ≠ R.parent := by
  rcases mem_BB_target_or_selected_or_blockingPoint
      (EqualInput L hL) M.paths hb with hselected | hblocking
  · exact Or.inl hselected
  · obtain ⟨F, hFG0, hblockable, hblock, hbF⟩ := hblocking
    refine Or.inr ⟨F, hFG0, hblockable, hblock, hbF, ?_⟩
    intro hparent
    exact R.fragment_not_mem_G0_of_parent_eq M hparent hFG0

end ReservedGroundedParent

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.targetMarkers_disjoint
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.exposedLadderPath_ne_parent
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.oldCollisionProvenance_not_mem_parent
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.CV_targetCollisionCut_disjoint_parent
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.parent_edgeSet_disjoint_CE_targetCollisionCut
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.sourceProxy_not_mem_targetCollisionCut
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.fragment_mem_HEmpty_of_parent_eq
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.BB_targetCollisionCut_disjoint_parent
#print axioms Erdos599.DWeb.KappaLadder.ReservedGroundedParent.mem_BB_target_or_selected_or_nonreserved_blockingPoint
