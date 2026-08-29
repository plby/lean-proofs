/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteSourceRoot
import ErdosProblems.Erdos599.GroundingErasedDecode
import ErdosProblems.Erdos599.GroundingForwardTailClassification

/-!
# Boundary geometry of grounded finite auxiliary sources

A finite source in the concrete auxiliary web is the terminal of a grounded
finite member of the limiting ladder.  Warp disjointness therefore shows
that no ladder edge can leave it.  In the repaired switched relation, any
edge leaving such a source must consequently be an actually inserted
forward edge; it cannot come from the residual ladder.

This isolates the remaining route-level obligation needed for the `CV`
part of the reachability-antichain proof.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode
open GroundingForwardTailClassification GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A grounded finite auxiliary source is terminal on its unique member of
the limiting ladder, so the original ladder relation has no outgoing edge
there. -/
theorem finiteSource_noOutgoing_familyEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource) :
    ¬ HasOutgoing (L.popularAuxiliaryInput hL.legal).familyEdges b := by
  obtain ⟨p, _hchosen, hpFinish, _hpSource, hpLimit⟩ :=
    L.exists_groundedFiniteParent_of_mem_finiteSource hL hb
  rintro ⟨y, hby⟩
  have hby' : ∃ q ∈ L.limitWarp, (b, y) ∈ q.edgeSet := by
    simpa only [PopularAuxiliary.Input.familyEdges,
      KappaLadder.popularAuxiliaryInput, Set.mem_ofPred_eq] using hby
  obtain ⟨q, hqLimit, hbyQ⟩ := hby'
  have hbQ : b ∈ q.support :=
    (q.edgeSet_subset_support_prod hbyQ).1
  have hbP : b ∈ _root_.Erdos599.DirectedPath.Path.support
      (Sum.inl p : Gamma.DPath) := by
    change b ∈ p.support
    rw [← hpFinish]
    exact p.finish_mem_support
  have hpq : (Sum.inl p : Gamma.DPath) = q :=
    DWeb.IsWarp.eq_of_mem_support
      (hL.legal.warpStages (Ladder.finalStage kappa)) hpLimit.1 hqLimit hbP hbQ
  subst q
  have hbyP : (b, y) ∈ p.edgeSet := by
    simpa using hbyQ
  exact
    (Alternating.FinitePath.source_ne_finish_of_mem_edgeSet p hbyP)
      hpFinish.symm

/-- In particular, no residual (cut-edge-deleted) ladder edge leaves a
grounded finite auxiliary source. -/
theorem finiteSource_noOutgoing_residualLadderEdges
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource) :
    ¬ HasOutgoing
      (residualLadderEdges (L.popularAuxiliaryIndexed hL) S) b := by
  rintro ⟨y, hby⟩
  exact L.finiteSource_noOutgoing_familyEdges hL hb ⟨y, hby.1⟩

/-- Thus every concrete switched edge leaving a grounded finite auxiliary
source is an inserted forward edge.  This is the exact remaining contact
class which must be excluded or ordered in the `CV` antichain argument. -/
theorem finiteSource_switchedEdge_mem_forward
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    {b y : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hby : (b, y) ∈ erasedSelectedSwitchedEdges
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S)) :
    (b, y) ∈ erasedSelectedDirectionEdges
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S) .forward := by
  rcases hby with hresidual | hforward
  · exact False.elim <| L.finiteSource_noOutgoing_residualLadderEdges
      hL S hb ⟨y, hresidual.1⟩
  · exact hforward.1

/-- Therefore the only remaining input needed to make a finite-source cut
point a sink is absence of an inserted forward departure. -/
theorem finiteSource_noOutgoing_switched_of_noForward
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hforward : ¬ HasOutgoing
      (erasedSelectedDirectionEdges (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S) .forward) b) :
    ¬ HasOutgoing
      (erasedSelectedSwitchedEdges (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S)) b := by
  rintro ⟨y, hy⟩
  exact hforward ⟨y, L.finiteSource_switchedEdge_mem_forward hL S hb hy⟩

/-- A grounded finite source which is itself an old cut point admits no
inserted forward departure.  The tail-classification leaves two cases.  An
edge gadget `b → v` contradicts terminality of the finite parent, while a
starting proxy containing `b` would identify a ray component with that
finite parent by warp disjointness. -/
theorem finiteSource_noOutgoing_forward_of_mem_cut
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut) :
    ¬ HasOutgoing
      (erasedSelectedDirectionEdges (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S) .forward) b := by
  intro hout
  have hbCV : b ∈ GroundingCut.CV
      (L.popularAuxiliaryInput hL.legal) S.cut :=
    GroundingCut.mem_CV.mpr hbCut
  rcases forwardOutgoing_at_CV_edge_or_startingProxy
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S) hbCV hout with
    ⟨c, v, d, hvd⟩ | ⟨c, i, d, _hstart, _hid, hbi⟩
  · let q := strongSelectedPath (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) (chosenRequest c.1)
    have hqStart : q.start ∈
        (L.popularAuxiliaryInput hL.legal).lambda.source :=
      (strongSelectedWarp (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S)).starts_in_source
          ⟨chosenRequest c.1, rfl⟩
    have hedgeSupport :
        PopularAuxiliary.Input.LambdaVertex.edge b v ∈ q.support :=
      (q.edgeSet_subset_support_prod hvd).1
    have hbvFamily : (b, v) ∈
        (L.popularAuxiliaryInput hL.legal).familyEdges :=
      (L.popularAuxiliaryInput hL.legal)
        |>.edgeNode_mem_familyEdges_of_start_in_source q hqStart hedgeSupport
    exact L.finiteSource_noOutgoing_familyEdges hL hb ⟨v, hbvFamily⟩
  · obtain ⟨p, _hchosen, hpFinish, _hpSource, hpLimit⟩ :=
      L.exists_groundedFiniteParent_of_mem_finiteSource hL hb
    have hbP : b ∈ _root_.Erdos599.DirectedPath.Path.support
        (Sum.inl p : Gamma.DPath) := by
      change b ∈ p.support
      rw [← hpFinish]
      exact p.finish_mem_support
    have hiLimit :
        (L.popularAuxiliaryInput hL.legal).proxyPath i ∈ L.limitWarp :=
      (L.popularAuxiliary_proxyPathsFaithful hL).1 i
    have heq : (Sum.inl p : Gamma.DPath) =
        (L.popularAuxiliaryInput hL.legal).proxyPath i :=
      DWeb.IsWarp.eq_of_mem_support
        (hL.legal.warpStages (Ladder.finalStage kappa))
          hpLimit.1 hiLimit hbP hbi
    obtain ⟨r, hr⟩ :=
      (L.popularAuxiliaryInput hL.legal).proxy_isRay i
    have : (Sum.inl p : Gamma.DPath) = Sum.inr r := heq.trans hr
    cases this

/-- Concrete sink theorem for the finite-source part of `CV`. -/
theorem finiteSource_noOutgoing_switched_of_mem_cut
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut) :
    ¬ HasOutgoing
      (erasedSelectedSwitchedEdges (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S)) b := by
  apply L.finiteSource_noOutgoing_switched_of_noForward hL S hb
  exact L.finiteSource_noOutgoing_forward_of_mem_cut hL S hb hbCut

end DWeb.KappaLadder
end Erdos599
