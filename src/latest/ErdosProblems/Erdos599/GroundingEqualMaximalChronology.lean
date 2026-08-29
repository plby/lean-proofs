/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingHangingCollisionSplit
import ErdosProblems.Erdos599.GroundingTargetPureChronology
import ErdosProblems.Erdos599.GroundingEqualMaximalRouteRoot

/-!
# Pathwise chronology for the maximal equal-stage family

The chronology proved for Assertion 8.19 is packaged around a local request
fan.  The maximal equal-stage construction instead uses arbitrary target-pure
paths in the grounding auxiliary web.  This file extracts the fan-independent
core: every hanging limiting component met at a decoded gadget exit has owner
stage at most the auxiliary source stage.

This is the rank invariant needed by an ordered active closure.  It does not
assert strict decrease: equality is precisely the genuine equal-stage branch.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder

open _root_.Erdos599.DirectedPath Ladder
open GroundingEqualActiveSelection

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A target-pure auxiliary path can meet a hanging limiting component only
at an owner stage weakly below its source stage.  The contact is stated using
the decoded gadget exit, so it applies uniformly to old and edge gadgets.

Unlike the request-fan version of Assertion 8.19, this theorem has no
separator, fan, or control parameter. -/
theorem targetPure_hangingComponentStage_le_of_gadgetExit_contact
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph)
    (hs : p.start ∈ (L.popularAuxiliaryInput hL.legal).lambda.source)
    (hpure : (L.popularAuxiliaryInput hL.legal).IsTargetPure p)
    {Y : Gamma.DPath} (hY : Y ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma Y)
    (z : (L.popularAuxiliaryInput hL.legal).LV)
    (hzp : z ∈ p.support)
    (v : V) (hvY : v ∈ Y.support)
    (hzexit : (L.popularAuxiliaryInput hL.legal).gadgetExit z = some v) :
    L.hangingComponentStage hL.legal Y hY hhang ≤
      (L.popularAuxiliaryIndexed hL).f ⟨p.start, hs⟩ := by
  let I := L.popularAuxiliaryInput hL.legal
  let U := L.popularAuxiliaryIndexed hL
  have hmeet : p.walk.Meets ({z} : Set I.LV) :=
    ⟨z, hzp, Set.mem_singleton z⟩
  let q : FinitePath I.lambda.graph :=
    p.firstHit ({z} : Set I.LV) hmeet
  have hqStart : q.start = p.start := rfl
  have hqFinish : q.finish = z := by
    exact Set.mem_singleton_iff.1
      (p.firstHit_finish_mem ({z} : Set I.LV) hmeet)
  have hqSource : q.start ∈ I.lambda.source := by
    rw [hqStart]
    exact hs
  have hqPure : I.IsTargetPure q :=
    PopularAuxiliary.Input.IsTargetPure.firstHit I hpure
      ({z} : Set I.LV) hmeet
  rcases I.start_of_mem_lambda_source p hs with
      ⟨x, hxSource, hpx⟩ | ⟨i, hpi⟩
  · let xg : L.groundedFiniteTerminalSet := ⟨x, hxSource⟩
    let xs : L.finiteTerminalSet :=
      ⟨x, L.groundedFiniteTerminalSet_subset_finiteTerminalSet xg.2⟩
    have hsourceIndex :
        U.f ⟨p.start, hs⟩ = L.finiteTerminalStage xs := by
      have hsEq :
          (⟨p.start, hs⟩ : I.lambda.source) =
            ⟨.old x, (I.mem_lambda_source_old x).2 hxSource⟩ :=
        Subtype.ext hpx
      rw [hsEq]
      rfl
    have hvRoof : v ∈ Gamma.roof
        (L.frontier (L.successorStage hL.legal
          (L.finiteTerminalStage xs))) :=
      hL.legal.targetPure_finite_gadgetExit_successorRoofTransport
        q hqSource hqPure xs z v (hqStart.trans hpx) hqFinish hzexit
    rw [hsourceIndex]
    exact hL.legal.hangingComponentStage_le_of_support_mem_roof_successor
      (L.finiteTerminalStage xs) hY hhang hvY hvRoof
  · have hsourceIndex :
        U.f ⟨p.start, hs⟩ = L.groundedInfiniteStage i := by
      have hsEq :
          (⟨p.start, hs⟩ : I.lambda.source) =
            ⟨.proxy i, I.mem_lambda_source_proxy i⟩ :=
        Subtype.ext hpi
      rw [hsEq]
      rfl
    have hvRoof : v ∈ Gamma.roof
        (L.frontier (L.successorStage hL.legal
          (L.groundedInfiniteStage i))) :=
      hL.legal.targetPure_proxy_gadgetExit_successorRoofTransport
        q hqSource hqPure i z v (hqStart.trans hpi) hqFinish hzexit
    rw [hsourceIndex]
    exact hL.legal.hangingComponentStage_le_of_support_mem_roof_successor
      (L.groundedInfiniteStage i) hY hhang hvY hvRoof

/-- Every backward edge retained by the canonical erased route still names
an edge gadget visited by the original auxiliary path. -/
theorem canonicalErasedRoute_backwardEdge_gadget_mem_support
    {I : Type u} (J : PopularAuxiliary.Input Gamma I)
    (Q : Popular.XSWarp J.lambda J.lambda.target)
    (p : WarpPath Q) {e : V × V}
    (he : e ∈ (canonicalErasedRoute J Q p).directionEdges .backward) :
    (PopularAuxiliary.Input.LambdaVertex.edge e.1 e.2 : J.LV) ∈
      p.1.support := by
  let T := J.decodeFinitePath p.1 (Q.starts_in_source p.2)
    (Q.ends_in_target p.2)
  let E := T.runs.erasedSignedRoute
  have he' : e ∈
      (E.compressionOfValid
        (fun {_s} hs ↦ T.valid _ (E.steps_sublist.subset hs))).path.directionEdges
          .backward := by
    simpa [canonicalErasedRoute, T, E,
      PopularAuxiliary.Input.MicroTrace.erasedCompression] using he
  have hsigned :=
    E.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
      (fun {_s} hs ↦ T.valid _ (E.steps_sublist.subset hs)) .backward he'
  obtain ⟨s, hsE, hsback, hse⟩ := hsigned
  have hsT : s ∈ T.steps := E.steps_sublist.subset hsE
  have hsRaw : s ∈ J.decodeWalkSteps p.1.walk := by
    simpa only [T, PopularAuxiliary.Input.decodeFinitePath_steps] using hsT
  have heRaw : e ∈ PopularAuxiliary.Input.directedSignedEdgeSet
      .backward (J.decodeWalkSteps p.1.walk) := by
    exact ⟨s, hsRaw, hsback, hse⟩
  rw [J.backwardEdges_decodeWalkSteps p.1.walk] at heRaw
  exact heRaw

/-- In the maximal equal-family decoder, every hanging owner of a compressed
backward link has rank weakly below the source rank of that route.  This is
the compressed-link form consumed by the finite alternating root theorem. -/
theorem canonicalErasedRoute_backwardLink_ownerStage_le_source
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (Q : Popular.XSWarp
      (L.popularAuxiliaryInput hL.legal).lambda
      (L.popularAuxiliaryInput hL.legal).lambda.target)
    (p : WarpPath Q)
    (hpure : (L.popularAuxiliaryInput hL.legal).IsTargetPure p.1)
    (l : Alternating.Link Gamma.graph)
    (hl : l ∈ (canonicalErasedRoute
      (L.popularAuxiliaryInput hL.legal) Q p).links)
    (hldir : l.direction = .backward)
    (parent : Gamma.DPath) (hparent : parent ∈ L.limitWarp)
    (hhang : PopularAuxiliary.IsHangingPath Gamma parent)
    (hsub : l.path.IsSubpathOf parent) :
    L.hangingComponentStage hL.legal parent hparent hhang ≤
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.1.start, Q.starts_in_source p.2⟩ := by
  obtain ⟨y, hy⟩ :=
    _root_.Erdos599.Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      l.path l.path.start_mem_support l.nontrivial
  have hyRoute : (l.path.start, y) ∈
      (canonicalErasedRoute
        (L.popularAuxiliaryInput hL.legal) Q p).directionEdges .backward := by
    simp only [Alternating.AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, hy⟩
  have hzSupport :
      (PopularAuxiliary.Input.LambdaVertex.edge l.path.start y :
          (L.popularAuxiliaryInput hL.legal).LV) ∈ p.1.support :=
    canonicalErasedRoute_backwardEdge_gadget_mem_support
      (L.popularAuxiliaryInput hL.legal) Q p hyRoute
  apply L.targetPure_hangingComponentStage_le_of_gadgetExit_contact hL
    p.1 (Q.starts_in_source p.2) hpure hparent hhang
      (.edge l.path.start y) hzSupport l.path.start
  · exact hsub.1 l.path.start_mem_support
  · rfl

end KappaLadder
end DWeb
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.targetPure_hangingComponentStage_le_of_gadgetExit_contact
