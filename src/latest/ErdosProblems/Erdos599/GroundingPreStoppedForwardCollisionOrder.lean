/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedResidualCollision
import ErdosProblems.Erdos599.GroundingSelectedForwardOrder

/-!
# The first selected edge in a pre-stopped collision

The pre-stopped relation retains all selected forward edges.  The existing
blocking-order theorem is phrased for the boundary-truncated retained
prefix; here we record the corresponding raw-forward form.  Combined with
the residual-prefix decomposition, the first selected departure after a
blocking point occurs either at that blocking point itself or at another
old cut vertex.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingPreStoppedForwardCollisionOrder

open Alternating GroundingErasedDecode GroundingSimultaneousDecode
  PopularAuxiliary.Input PopularGroundingBridge

universe u

variable {V I : Type u} {Gamma : DWeb V}

/-- Raw selected-forward analogue of the retained-tail order theorem. -/
theorem selectedForwardTail_beforeEq_or_mem_CV
    {L : PopularAuxiliary.Input Gamma I} {kappa : Cardinal.{u}}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) (r : Request L S.cut)
    (hfaith : ProxyPathsFaithful L)
    (P : L.Fragment) (hP : P ∈ GroundingCut.G0 L S.cut)
    (hblockable : GroundingCut.IsBlockable L S.cut P)
    {b y : V}
    (hby : (b, y) ∈
      (selectedErasedCompression U S K r).path.directionEdges .forward)
    (hbP : b ∈ P.path.support) :
    GroundingCut.BeforeEq P.path b
        (GroundingCut.blockingPoint L S.cut P) ∨
      b ∈ GroundingCut.CV L S.cut := by
  rcases
      GroundingForwardTailClassification.selectedForwardTail_old_or_edge_or_startingProxy
        U S K r hby with hold | hedge | hproxy
  · obtain ⟨d, hbd⟩ := hold
    have hbSupport : (LambdaVertex.old b : L.LV) ∈
        (strongSelectedPath U S K r).support :=
      ((strongSelectedPath U S K r).edgeSet_subset_support_prod hbd).1
    by_cases hbApex :
        (LambdaVertex.old b : L.LV) = requestAuxVertex r
    · exact Or.inr <| GroundingCut.mem_CV.mpr <|
        hbApex ▸ requestAuxVertex_mem_cut r
    · exact Or.inl <|
        GroundingDecodedContactOrder.strongSelectedPath_fragmentContact_beforeEq_blockingPoint
          S K r P hP hblockable ⟨⟨hbSupport, hbApex⟩, hbP⟩
  · obtain ⟨v, d, hvd⟩ := hedge
    have hedgeSupport : (LambdaVertex.edge b v : L.LV) ∈
        (strongSelectedPath U S K r).support :=
      ((strongSelectedPath U S K r).edgeSet_subset_support_prod hvd).1
    have hedgeNotApex :
        (LambdaVertex.edge b v : L.LV) ≠ requestAuxVertex r := by
      intro hedgeApex
      have hfinish := strongSelectedPath_finish U S K r
      exact (Alternating.FinitePath.source_ne_finish_of_mem_edgeSet
        (strongSelectedPath U S K r) hvd)
          (hedgeApex.trans hfinish.symm)
    exact
      GroundingSelectedBackwardOrder.strongSelectedPath_edgeGadgetTail_beforeEq_or_mem_CV
        U S K r P hP hblockable hedgeSupport hedgeNotApex hbP
  · obtain ⟨i, _d, hstart, _hid, hbi⟩ := hproxy
    exact GroundingSelectedForwardOrder.startingProxyTail_beforeEq_or_mem_CV
      U S K r hfaith P hP hblockable hbP hstart hbi

end GroundingPreStoppedForwardCollisionOrder

namespace DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- If the first nonresidual edge after a blocking point is selected
forward, then its tail is the blocking point itself or another member of
`CV`. -/
theorem firstSelectedForwardTail_eq_earlier_or_mem_CV
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R)
    (P : (L.popularAuxiliaryInput hL.legal).Fragment)
    (hPG0 : P ∈ GroundingCut.G0
      (L.popularAuxiliaryInput hL.legal) S.cut)
    (hblockable : GroundingCut.IsBlockable
      (L.popularAuxiliaryInput hL.legal) S.cut P)
    (hearlier : GroundingCut.blockingPoint
      (L.popularAuxiliaryInput hL.legal) S.cut P = o.earlier)
    (c : ActiveControlRequestAt
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) (∅ : Set V))
    {u v : V}
    (hprefix : Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈ residualLadderEdges
        (L.popularAuxiliaryIndexed hL) S) o.earlier u)
    (huv : (u, v) ∈ (selectedErasedCompression
      (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R)
      (chosenRequest c.1)).path.directionEdges .forward) :
    u = o.earlier ∨
      u ∈ GroundingCut.CV (L.popularAuxiliaryInput hL.legal) S.cut := by
  have hearlierSupport : o.earlier ∈ P.path.support := by
    rw [← hearlier]
    exact GroundingCut.blockingPoint_mem_support
      (L.popularAuxiliaryInput hL.legal) S.cut P
  obtain ⟨huP, hearlierBefore⟩ :=
    GroundingFragmentResidualOrder.mem_and_beforeEq_of_reflTransGen_residualLadderEdges
      (L.popularAuxiliaryIndexed hL) S hPG0.1 hearlierSupport hprefix
  rcases
      GroundingPreStoppedForwardCollisionOrder.selectedForwardTail_beforeEq_or_mem_CV
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) (chosenRequest c.1)
        (L.popularAuxiliary_proxyPathsFaithful hL) P hPG0 hblockable
        huv huP with huBefore | huCV
  · left
    have hearlierEq : o.earlier = u := by
      apply GroundingCutDecoder.beforeEq_antisymm hearlierBefore
      simpa only [hearlier] using huBefore
    exact hearlierEq.symm
  · exact Or.inr huCV

end DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction
end Erdos599

#print axioms Erdos599.GroundingPreStoppedForwardCollisionOrder.selectedForwardTail_beforeEq_or_mem_CV
#print axioms Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.firstSelectedForwardTail_eq_earlier_or_mem_CV
