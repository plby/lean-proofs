/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryFirstHit
import ErdosProblems.Erdos599.GroundingForwardTailClassification

/-!
# The finite-source endpoint cannot begin a grounded split boundary collision

A finite source of the grounded auxiliary is the terminal of its canonical
finite member of the limiting warp.  Split legality supplies the same warp
disjointness used by the construction, while cut membership excludes every
possible selected forward departure.  Hence it is a sink even in the raw
pre-stopped relation.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open Alternating PopularGroundingBridge GroundingErasedDecode
open GroundingForwardTailClassification GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev GroundedSinkInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev GroundedSinkIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- The canonical finite parent makes a finite cut source terminal in the
limiting family. -/
theorem SplitGroundedUnusedRecord.finiteSource_noOutgoing_familyEdges
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    {b : V}
    (hb : b ∈ (GroundedSinkInput (L := L) (hL := hL)).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut) :
    ¬ HasOutgoing
      (GroundedSinkInput (L := L) (hL := hL)).familyEdges b := by
  obtain ⟨p, _hchosen, hpFinish, _hpSource, hpLimit⟩ :=
    R.exists_cutFiniteSource_parent_with_allowed_root hb hbCut
  rintro ⟨y, hby⟩
  have hby' : ∃ q ∈ L.limitWarp, (b, y) ∈ q.edgeSet := by
    simpa only [PopularAuxiliary.Input.familyEdges,
      splitGroundedPopularAuxiliaryInput, Set.mem_ofPred_eq] using hby
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
  have hbyP : (b, y) ∈ p.edgeSet := by simpa using hbyQ
  exact (Alternating.FinitePath.source_ne_finish_of_mem_edgeSet p hbyP)
    hpFinish.symm

/-- No residual ladder edge leaves a finite cut source. -/
theorem SplitGroundedUnusedRecord.finiteSource_noOutgoing_residual
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    {b : V}
    (hb : b ∈ (GroundedSinkInput (L := L) (hL := hL)).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut) :
    ¬ HasOutgoing
      (residualLadderEdges
        (GroundedSinkIndexed (L := L) (hL := hL) (hground := hground)) S) b := by
  rintro ⟨y, hby⟩
  exact R.finiteSource_noOutgoing_familyEdges hb hbCut ⟨y, hby.1⟩

/-- No selected forward edge in the pre-stopped switch leaves a finite old
source represented in the cut.  The only two decoder cases contradict
terminality of its finite parent or finite/ray disjointness in the limiting
warp. -/
theorem SplitGroundedUnusedRecord.finiteSource_noOutgoing_forwardAt_empty
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    {b : V}
    (hb : b ∈ (GroundedSinkInput (L := L) (hL := hL)).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut) :
    ¬ HasOutgoing
      (erasedSelectedDirectionEdgesAt
        (GroundedSinkIndexed (L := L) (hL := hL) (hground := hground))
          S K ∅ .forward) b := by
  intro hout
  have hbCV : b ∈ GroundingCut.CV
      (GroundedSinkInput (L := L) (hL := hL)) S.cut :=
    GroundingCut.mem_CV.mpr hbCut
  obtain ⟨y, hby⟩ := hout
  simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion] at hby
  obtain ⟨c, hby⟩ := hby
  rcases selectedForwardTail_at_CV_edge_or_startingProxy
      (GroundedSinkIndexed (L := L) (hL := hL) (hground := hground))
        S K (chosenRequest c.1) hbCV hby with
    ⟨v, d, hvd⟩ | ⟨i, d, _hstart, _hid, hbi⟩
  · let q := strongSelectedPath
      (GroundedSinkIndexed (L := L) (hL := hL) (hground := hground))
        S K (chosenRequest c.1)
    have hqStart : q.start ∈
        (GroundedSinkInput (L := L) (hL := hL)).lambda.source :=
      (strongSelectedWarp
        (GroundedSinkIndexed (L := L) (hL := hL) (hground := hground))
          S K).starts_in_source ⟨chosenRequest c.1, rfl⟩
    have hedgeSupport :
        PopularAuxiliary.Input.LambdaVertex.edge b v ∈ q.support :=
      (q.edgeSet_subset_support_prod hvd).1
    have hbvFamily : (b, v) ∈
        (GroundedSinkInput (L := L) (hL := hL)).familyEdges :=
      (GroundedSinkInput (L := L) (hL := hL))
        |>.edgeNode_mem_familyEdges_of_start_in_source q hqStart hedgeSupport
    exact R.finiteSource_noOutgoing_familyEdges hb hbCut ⟨v, hbvFamily⟩
  · obtain ⟨p, _hchosen, hpFinish, _hpSource, hpLimit⟩ :=
      R.exists_cutFiniteSource_parent_with_allowed_root hb hbCut
    have hbP : b ∈ _root_.Erdos599.DirectedPath.Path.support
        (Sum.inl p : Gamma.DPath) := by
      change b ∈ p.support
      rw [← hpFinish]
      exact p.finish_mem_support
    have hiLimit :
        (GroundedSinkInput (L := L) (hL := hL)).proxyPath i ∈ L.limitWarp :=
      (L.splitGroundedPopularAuxiliary_proxyPathsFaithful hL).1 i
    have heq : (Sum.inl p : Gamma.DPath) =
        (GroundedSinkInput (L := L) (hL := hL)).proxyPath i :=
      DWeb.IsWarp.eq_of_mem_support
        (hL.legal.warpStages (Ladder.finalStage kappa))
          hpLimit.1 hiLimit hbP hbi
    obtain ⟨r, hr⟩ :=
      (GroundedSinkInput (L := L) (hL := hL)).proxy_isRay i
    have : (Sum.inl p : Gamma.DPath) = Sum.inr r := heq.trans hr
    cases this

/-- A finite cut source is a sink of the literal pre-stopped relation. -/
theorem SplitGroundedUnusedRecord.finiteSource_noOutgoing_preStopped
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    {b : V}
    (hb : b ∈ (GroundedSinkInput (L := L) (hL := hL)).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut) :
    ¬ HasOutgoing
      (erasedSelectedSwitchedEdgesAt
        (GroundedSinkIndexed (L := L) (hL := hL) (hground := hground))
          S K ∅) b := by
  intro hout
  obtain ⟨y, hby⟩ := hout
  rw [erasedSelectedSwitchedEdgesAt_empty_eq] at hby
  rcases hby with hresidual | hforward
  · exact R.finiteSource_noOutgoing_residual hb hbCut ⟨y, hresidual.1⟩
  · exact R.finiteSource_noOutgoing_forwardAt_empty hb hbCut ⟨y, hforward⟩

/-- Therefore the earlier endpoint in a nontrivial ordered boundary
obstruction cannot have a finite-source owner. -/
theorem SplitGroundedPreStoppedBoundaryObstruction.earlier_not_finiteSource
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (O : L.SplitGroundedPreStoppedBoundaryObstruction R)
    (hfinite : O.earlier ∈
      (GroundedSinkInput (L := L) (hL := hL)).finiteSource)
    (hcut : PopularAuxiliary.Input.LambdaVertex.old O.earlier ∈ S.cut) :
    False := by
  apply O.distinct
  exact GroundingBlockingReachability.eq_of_reflTransGen_of_noOutgoing
    (R.finiteSource_noOutgoing_preStopped hfinite hcut) O.reaches

/-- First-hit boundary normal form after the impossible finite-source first
endpoint has been removed.  The later endpoint remains fully classified,
so these two constructors represent exactly the six control/blocking to
finite/control/blocking owner pairs. -/
inductive SplitGroundedFirstBoundarySinkOutcome
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (O : L.SplitGroundedPreStoppedBoundaryObstruction R) : Prop
  | earlierControl
      (D : L.SplitGroundedFirstBoundaryReduction R O)
      (old : oldRequests
        (GroundedSinkInput (L := L) (hL := hL)) S.cut)
      (value_eq : old.1 = D.reduced.earlier)
      (later_owner : SplitGroundedBBPointOwner
        (L := L) (hL := hL) (hground := hground) (S := S)
          D.reduced.later)
  | earlierBlocking
      (D : L.SplitGroundedFirstBoundaryReduction R O)
      (P : (GroundedSinkInput (L := L) (hL := hL)).Fragment)
      (fragment_mem : P ∈ GroundingCut.G0
        (GroundedSinkInput (L := L) (hL := hL)) S.cut)
      (blockable : GroundingCut.IsBlockable
        (GroundedSinkInput (L := L) (hL := hL)) S.cut P)
      (point_eq : GroundingCut.blockingPoint
        (GroundedSinkInput (L := L) (hL := hL)) S.cut P =
          D.reduced.earlier)
      (point_mem_support : D.reduced.earlier ∈ P.path.support)
      (later_owner : SplitGroundedBBPointOwner
        (L := L) (hL := hL) (hground := hground) (S := S)
          D.reduced.later)

/-- Produce the six-case first-boundary normal form. -/
theorem SplitGroundedPreStoppedBoundaryObstruction.firstBoundarySinkOutcome
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (O : L.SplitGroundedPreStoppedBoundaryObstruction R) :
    SplitGroundedFirstBoundarySinkOutcome R O := by
  obtain ⟨D⟩ := O.exists_firstBoundaryOwnerPair R
  cases D.earlier_owner with
  | finiteSource hfinite hcut =>
      exact False.elim
        (D.reduction.reduced.earlier_not_finiteSource R hfinite hcut)
  | oldControl old hvalue =>
      exact .earlierControl D.reduction old hvalue D.later_owner
  | blocking P hPG0 hblockable hpoint hsupport =>
      exact .earlierBlocking D.reduction P hPG0 hblockable hpoint hsupport
        D.later_owner

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedUnusedRecord.finiteSource_noOutgoing_preStopped
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedPreStoppedBoundaryObstruction.earlier_not_finiteSource
#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedPreStoppedBoundaryObstruction.firstBoundarySinkOutcome
