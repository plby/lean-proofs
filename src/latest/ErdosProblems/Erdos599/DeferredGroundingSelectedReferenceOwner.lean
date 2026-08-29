/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingEssentialHangingBackward
import ErdosProblems.Erdos599.GroundingErasedSwitchRelation

/-!
# Owners contacted by the final deferred selected route

An actual decoded contact with an essential limiting component cannot be
hidden solely in the initial proxy: that proxy represents the selected
starting record, which is inessential.  Hence an essential contacted owner
is either grounded, or is a hanging owner met by the auxiliary route.  In
the latter case deferred equal-collision normalization puts the literal
request apex on its trace.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath Ladder Stationary
open PopularGroundingBridge GroundingSimultaneousDecode
open Alternating PopularAuxiliary.Input GroundingErasedDecode
open GroundingErasedSwitchRelation

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- If a request apex lies on a ladder trace, its decoded exit is a vertex
of the same owner.  For an edge request the exit is the head of the traced
ladder edge. -/
theorem requestExit_mem_support_of_requestAuxVertex_mem_ladderTrace
    {I : Type u} (J : PopularAuxiliary.Input Gamma I) {C : Set J.LV}
    (r : Request J C) (Y : Gamma.DPath)
    (h : requestAuxVertex r ∈ PopularSwitching.ladderTrace J Y) :
    requestExit r ∈ Y.support := by
  cases r with
  | inl x =>
      exact (PopularSwitching.old_mem_ladderTrace_iff J Y x.1).1 h
  | inr e =>
      have heY :=
        (PopularSwitching.edge_mem_ladderTrace_iff J Y e.1.1 e.1.2).1 h
      exact (Y.edgeSet_subset_support_prod heY).2

/-- Within one reference warp, an owner containing the request apex is the
displayed terminal owner whenever the request exit is that owner's initial
vertex. -/
theorem eq_terminalOwner_of_requestAuxVertex_mem_ladderTrace
    {I : Type u} (J : PopularAuxiliary.Input Gamma I) {C : Set J.LV}
    (r : Request J C) {W : Set Gamma.DPath}
    (hW : Gamma.IsWarp W) (Y Z : Gamma.DPath)
    (hY : Y ∈ W) (hZ : Z ∈ W)
    (hapex : requestAuxVertex r ∈ PopularSwitching.ladderTrace J Y)
    (hexit : requestExit r = Z.initial) :
    Y = Z := by
  apply DWeb.IsWarp.eq_of_mem_support hW hY hZ
      (requestExit_mem_support_of_requestAuxVertex_mem_ladderTrace
        J r Y hapex)
  rw [hexit]
  exact Z.initial_mem_support

private theorem selectedDirectionEdge_mem_edgeSet
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed J.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request J S.cut) (d : Direction) {e : V × V}
    (he : e ∈ (selectedErasedCompression U S K r).path.directionEdges d) :
    e ∈ (selectedErasedCompression U S K r).path.edgeSet := by
  rw [(selectedErasedCompression U S K r).path.edgeSet_eq_directionEdges_union]
  cases d with
  | forward => exact Or.inl he
  | backward => exact Or.inr he

private theorem selectedDirectionVertex_mem_decodedVertexCarrier
    {I : Type u} {J : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed J.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request J S.cut) (d : Direction) {x : V}
    (hx : x ∈ (selectedErasedCompression U S K r).path.directionVertices d) :
    x ∈ J.decodedVertexCarrier (strongSelectedPath U S K r) := by
  simp only [AltPath.directionVertices, Set.mem_iUnion] at hx
  obtain ⟨l, hl, hldir, hxl⟩ := hx
  obtain ⟨e, hel, hxe⟩ :
      ∃ e ∈ l.path.edgeSet, x = e.1 ∨ x = e.2 := by
    by_cases hxfinish : x = l.path.finish
    · have hxstart : x ≠ l.path.start := by
        intro h
        apply l.nontrivial
        exact h.symm.trans hxfinish
      obtain ⟨y, hy⟩ :=
        FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
          l.path hxl hxstart
      exact ⟨(y, x), hy, Or.inr rfl⟩
    · obtain ⟨y, hy⟩ :=
        FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
          l.path hxl hxfinish
      exact ⟨(x, y), hy, Or.inl rfl⟩
  have heDir : e ∈
      (selectedErasedCompression U S K r).path.directionEdges d := by
    simp only [AltPath.directionEdges, Set.mem_iUnion]
    exact ⟨l, hl, hldir, hel⟩
  have hePath := selectedDirectionEdge_mem_edgeSet U S K r d heDir
  have heCarrier :=
    selectedErasedRouteEdge_endpoints_mem U S K r hePath
  exact hxe.elim (fun h ↦ h.symm ▸ heCarrier.1)
    (fun h ↦ h.symm ▸ heCarrier.2)

/-- A decoded contact with an essential owner is either already grounded,
or is attached to the selected request at its literal auxiliary apex. -/
theorem canonicalDeferredLadder_reservedStrongSelected_essentialOwner_contact_grounded_or_apex
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (Y : Gamma.DPath)
    (hY : Y ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder Gamma kappa preferred) hL.legal).essentialLadder)
    {x : V}
    (hxSelected : x ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder Gamma kappa preferred) hL.legal).decodedVertexCarrier
        (strongSelectedPath
          (popularAuxiliaryIndexed
            (canonicalDeferredLadder Gamma kappa preferred) hL)
          S (reservedGroundedCarrierControls
            (canonicalDeferredLadder Gamma kappa preferred) hL S) r))
    (hxY : x ∈ Y.support) :
    Y.initial ∈ Gamma.source ∨
      requestAuxVertex r ∈ PopularSwitching.ladderTrace
        (popularAuxiliaryInput
          (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  let J := popularAuxiliaryInput L hL.legal
  let U := popularAuxiliaryIndexed L hL
  let K := reservedGroundedCarrierControls L hL S
  let p := strongSelectedPath U S K r
  let R := reservedStrongSelectedStartingRecord r
  have hpSource : p.start ∈ J.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩
  have hYEssential : Y ∈ Gamma.essentialWarpPart L.limitWarp := by
    simpa only [J, popularAuxiliaryInput,
      PopularAuxiliary.Input.essentialLadder, limitWarp] using hY
  have hYLimit : Y ∈ L.limitWarp := by
    exact hYEssential.1
  have hYExposed : Y ∈ exposedLadderPaths J p :=
    J.mem_exposedLadderPaths_of_mem_decodedVertexCarrier_of_mem_support
      (popularAuxiliary_proxyPathsFaithful L hL) p hpSource hYLimit
      hxSelected hxY
  have hYMeet : p.walk.Meets (PopularSwitching.ladderTrace J Y) := by
    rcases hYExposed with hmet | hproxy
    · obtain ⟨_hY, z, hzp, hzY⟩ := hmet
      exact ⟨z, hzp, hzY⟩
    · have hproxyData : ∃ i, p.start = .proxy i ∧ Y = J.proxyPath i := by
        generalize hs : p.start = s at hproxy ⊢
        cases s with
        | old z => simp [exposedLadderPaths] at hproxy
        | edge z w => simp [exposedLadderPaths] at hproxy
        | proxy i =>
            refine ⟨i, rfl, ?_⟩
            simpa [exposedLadderPaths] using hproxy
      obtain ⟨i, hstart, hYProxy⟩ := hproxyData
      have hsource : (reservedStrongSelectedSource r).1 = .proxy i := by
        exact hstart
      rcases R.represents with ⟨q, hRq, hsourceOld⟩ |
          ⟨j, hRj, hsourceProxy⟩
      · rw [hsource] at hsourceOld
        cases hsourceOld
      · have hji : j = i := by
          exact PopularAuxiliary.Input.LambdaVertex.proxy.inj
            (hsourceProxy.symm.trans hsource)
        subst j
        have hrecord : R.record = J.proxyPath i := by
          exact hRj
        have hYInessential : Y ∈ Gamma.inessentialPaths L.limitWarp := by
          rw [hYProxy, ← hrecord]
          exact R.limit_inessential
        exact False.elim (hYInessential.2 hYEssential)
  rcases PopularAuxiliary.grounded_or_hanging Gamma Y with
      hgrounded | hhanging
  · exact Or.inl hgrounded
  · exact Or.inr
      (canonicalDeferredLadder_reservedStrongSelected_meets_essentialHanging_apex_mem
        preferred hkappa huncountable hNoEnter hL S r Y hY hhanging hYMeet)

/-- Concrete forward-reference form.  If a retained selected forward edge
also belongs to an essential limiting component, that component is grounded
or is attached at the selected request apex. -/
theorem canonicalDeferredLadder_reservedStrongSelected_forwardReferenceOwner_grounded_or_apex
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (Y : Gamma.DPath)
    (hY : Y ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder Gamma kappa preferred) hL.legal).essentialLadder)
    {e : V × V}
    (heForward : e ∈
      (selectedErasedCompression
        (popularAuxiliaryIndexed
          (canonicalDeferredLadder Gamma kappa preferred) hL)
        S (reservedGroundedCarrierControls
          (canonicalDeferredLadder Gamma kappa preferred) hL S) r).path.directionEdges
        .forward)
    (heY : e ∈ Y.edgeSet) :
    Y.initial ∈ Gamma.source ∨
      requestAuxVertex r ∈ PopularSwitching.ladderTrace
        (popularAuxiliaryInput
          (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  let J := popularAuxiliaryInput L hL.legal
  let U := popularAuxiliaryIndexed L hL
  let K := reservedGroundedCarrierControls L hL S
  have hePath : e ∈ (selectedErasedCompression U S K r).path.edgeSet :=
    selectedDirectionEdge_mem_edgeSet U S K r .forward heForward
  have heCarrier := selectedErasedRouteEdge_endpoints_mem U S K r hePath
  exact
    canonicalDeferredLadder_reservedStrongSelected_essentialOwner_contact_grounded_or_apex
      preferred hkappa huncountable hNoEnter hL S r Y hY heCarrier.1
      (Y.edgeSet_subset_support_prod heY).1

/-- Concrete vertex-contact form used by the uncovered-contact terminal
branch.  A selected forward vertex on an essential limiting component has
the same grounded-or-apex classification. -/
theorem canonicalDeferredLadder_reservedStrongSelected_forwardVertexOwner_grounded_or_apex
    (preferred : Stage kappa → Option V)
    (hkappa : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNoEnter : Gamma.NoEdgeEnters Gamma.source)
    (hL : IsKappaHindrance
      (canonicalDeferredLadder Gamma kappa preferred))
    (S : Popular.PopularSeparator
      (popularAuxiliaryIndexed
        (canonicalDeferredLadder Gamma kappa preferred) hL))
    (r : Request
      (popularAuxiliaryInput
        (canonicalDeferredLadder Gamma kappa preferred) hL.legal) S.cut)
    (Y : Gamma.DPath)
    (hY : Y ∈ (popularAuxiliaryInput
      (canonicalDeferredLadder Gamma kappa preferred) hL.legal).essentialLadder)
    {x : V}
    (hxForward : x ∈
      (selectedErasedCompression
        (popularAuxiliaryIndexed
          (canonicalDeferredLadder Gamma kappa preferred) hL)
        S (reservedGroundedCarrierControls
          (canonicalDeferredLadder Gamma kappa preferred) hL S) r).path.directionVertices
        .forward)
    (hxY : x ∈ Y.support) :
    Y.initial ∈ Gamma.source ∨
      requestAuxVertex r ∈ PopularSwitching.ladderTrace
        (popularAuxiliaryInput
          (canonicalDeferredLadder Gamma kappa preferred) hL.legal) Y := by
  let L := canonicalDeferredLadder Gamma kappa preferred
  let J := popularAuxiliaryInput L hL.legal
  let U := popularAuxiliaryIndexed L hL
  let K := reservedGroundedCarrierControls L hL S
  have hxCarrier : x ∈ J.decodedVertexCarrier
      (strongSelectedPath U S K r) :=
    selectedDirectionVertex_mem_decodedVertexCarrier U S K r .forward
      hxForward
  exact
    canonicalDeferredLadder_reservedStrongSelected_essentialOwner_contact_grounded_or_apex
      preferred hkappa huncountable hNoEnter hL S r Y hY hxCarrier hxY

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.requestExit_mem_support_of_requestAuxVertex_mem_ladderTrace
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.eq_terminalOwner_of_requestAuxVertex_mem_ladderTrace
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalDeferredLadder_reservedStrongSelected_essentialOwner_contact_grounded_or_apex
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalDeferredLadder_reservedStrongSelected_forwardReferenceOwner_grounded_or_apex
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalDeferredLadder_reservedStrongSelected_forwardVertexOwner_grounded_or_apex
