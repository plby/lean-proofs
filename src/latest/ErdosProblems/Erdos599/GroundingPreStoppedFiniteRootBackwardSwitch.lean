/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteBackwardTerminalContact
import ErdosProblems.Erdos599.GroundingPreStoppedBackwardNormalizedCompiler

/-!
# Backward normalization of a finite pre-stopped root obstruction

An unrooted finite auxiliary source has a canonical grounded finite parent.
Its genuine initial is an allowed original source, distinct from the
stationarily reserved source.  Consequently that parent cannot be trivial:
otherwise the boundary point would already be rooted by reflexivity.

The whole parent therefore supplies the same one-link backward
terminal-contact normalization as a finite boundary collision.  This file
propagates that normalization into the total root-failure classifier and
then combines the normalized root and collision classifiers in one public
Assertion 8.22 compiler.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedRootObstruction

/-- Complete source and switching data extracted from the finite constructor
of an unrooted pre-stopped boundary point. -/
structure FiniteRootBackwardSwitchData
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) where
  finiteSource : O.boundary ∈
    (L.popularAuxiliaryInput hL.legal).finiteSource
  cut : (PopularAuxiliary.Input.LambdaVertex.old O.boundary :
    (L.popularAuxiliaryInput hL.legal).LV) ∈ S.cut
  parent : _root_.Erdos599.DirectedPath.FinitePath Gamma.graph
  chosen : L.chosen (L.finiteTerminalIndex
    ⟨O.boundary, finiteSource⟩) = some (.inl parent : Gamma.DPath)
  finish : parent.finish = O.boundary
  source : parent.start ∈ Gamma.source
  limit_inessential : (.inl parent : Gamma.DPath) ∈
    Gamma.inessentialPaths L.limitWarp
  source_ne_reserved : parent.start ≠ R.record.initial
  nontrivial : parent.start ≠ parent.finish
  trace : FiniteTrace Gamma.graph
  switching : IsTerminalContactSwitching
    (L.popularAuxiliaryInput hL.legal).ladder.paths trace parent.start
  trace_initial : trace.initial = O.boundary

/-- A finite root obstruction has a canonical nontrivial grounded parent,
and the whole-parent backward traversal normalizes it to a terminal-contact
switch whose terminal is an allowed original source. -/
theorem exists_finiteRootBackwardSwitchData
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R)
    (hfinite : O.boundary ∈
      (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hcut : (PopularAuxiliary.Input.LambdaVertex.old O.boundary :
      (L.popularAuxiliaryInput hL.legal).LV) ∈ S.cut) :
    Nonempty (FiniteRootBackwardSwitchData O) := by
  obtain ⟨p, hchosen, hfinish, hsource, hlimit, hrootNe⟩ :=
    R.exists_cutFiniteSource_parent_with_root_ne hfinite hcut
  have hnontrivial : p.start ≠ p.finish := by
    intro htrivial
    apply O.not_rooted
    refine ⟨p.start, ⟨hsource, hrootNe.symm⟩, ?_⟩
    have hstartBoundary : p.start = O.boundary :=
      htrivial.trans hfinish
    rw [← hstartBoundary]
  have hpLadder : (Sum.inl p : Gamma.DPath) ∈
      (L.popularAuxiliaryInput hL.legal).ladder.paths := by
    simpa only [KappaLadder.popularAuxiliaryInput] using hlimit.1
  obtain ⟨Q, hswitch, hQinitial⟩ :=
    exists_wholePathBackwardTerminalContactSwitching
      (L.popularAuxiliaryInput hL.legal).ladder.paths
      (L.popularAuxiliaryInput hL.legal).ladder.2 p hpLadder hnontrivial
  exact ⟨{
    finiteSource := hfinite
    cut := hcut
    parent := p
    chosen := hchosen
    finish := hfinish
    source := hsource
    limit_inessential := hlimit
    source_ne_reserved := hrootNe.symm
    nontrivial := hnontrivial
    trace := Q
    switching := hswitch
    trace_initial := hQinitial.trans hfinish }⟩

/-- Realizing the canonical backward switch removes exactly the grounded
parent's genuine source and the finite boundary at which the root
obstruction was detected. -/
theorem FiniteRootBackwardSwitchData.exists_terminalContactWarp
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    (data : FiniteRootBackwardSwitchData O) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
        Gamma.initialSet W =
          Gamma.initialSet
              (L.popularAuxiliaryInput hL.legal).ladder.paths \
                {data.parent.start} ∧
        Gamma.terminalFrontier W =
          Gamma.terminalFrontier
              (L.popularAuxiliaryInput hL.legal).ladder.paths \
                {O.boundary} := by
  have hboundary : O.boundary ∈ Gamma.terminalFrontier
      (L.popularAuxiliaryInput hL.legal).ladder.paths := by
    refine ⟨Sum.inl data.parent, ?_, ?_⟩
    · simpa only [KappaLadder.popularAuxiliaryInput] using
        data.limit_inessential.1
    · simpa only [DWeb.terminal?_finite, data.finish]
  exact TerminalContactSwitch.exists_terminalContactSwitch_anyWarp
    (L.popularAuxiliaryInput hL.legal).ladder.paths data.trace
      data.parent.start O.boundary data.switching hboundary
        data.trace_initial

/-- Once the realized canonical finite-root exchange is a wave, the
removed genuine source makes it an ordinary hindrance. -/
theorem FiniteRootBackwardSwitchData.exists_hindrance_of_terminalContactWarp_isWave
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedRootObstruction hL S R}
    (data : FiniteRootBackwardSwitchData O)
    (wave : ∀ W : Set Gamma.DPath,
      Gamma.IsWarp W →
      Gamma.initialSet W =
        Gamma.initialSet
            (L.popularAuxiliaryInput hL.legal).ladder.paths \
              {data.parent.start} →
      Gamma.terminalFrontier W =
        Gamma.terminalFrontier
            (L.popularAuxiliaryInput hL.legal).ladder.paths \
              {O.boundary} →
      Gamma.IsWave W) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  obtain ⟨W, hwarp, hinitial, hterminal⟩ :=
    data.exists_terminalContactWarp
  refine ⟨W, wave W hwarp hinitial hterminal, ?_⟩
  intro heq
  have hsource : data.parent.start ∈ Gamma.initialSet W :=
    heq.symm ▸ data.source
  rw [hinitial] at hsource
  exact hsource.2 rfl

/-- The total root-failure classifier with its finite constructor already
normalized by the whole grounded parent. -/
inductive BackwardNormalizedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) : Prop
  | normalizedFinite (data : FiniteRootBackwardSwitchData O)
  | activeControl
      (c : GroundingErasedDecode.ControlRequest
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : c.1 = O.boundary)
      (active : GroundingErasedDecode.IsActiveControlAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅ c)
  | activeRetainedVertex
      (c : GroundingErasedDecode.ControlRequest
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : c.1 = O.boundary)
      (d : GroundingErasedDecode.ActiveControlRequestAt
        (L.popularAuxiliaryIndexed hL) S
        (L.reservedGroundedControls hL S R) ∅)
      (x : V)
      (retained : x ∈ GroundingErasedDecode.retainedForwardVerticesAt ∅
        (GroundingErasedDecode.selectedErasedCompression
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R)
          (GroundingErasedDecode.chosenRequest d.1)).path)
      (not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun u v ↦ (u, v) ∈
            L.assertion822ReservedPreStoppedEdges hL S R) a x)
  | inactiveControl
      (c : GroundingErasedDecode.ControlRequest
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : c.1 = O.boundary)
      (data : InactivePreStoppedRootObstructionData S
        (L.reservedGroundedControls hL S R)
        (Gamma.source \ {R.record.initial}) c)
  | blockingInitial
      (P : (L.popularAuxiliaryInput hL.legal).Fragment)
      (blockable : P ∈ GroundingCut.blockableG0
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary)
      (initial_not_rooted : ¬ ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈
            L.assertion822ReservedPreStoppedEdges hL S R)
          a P.path.initial)
  | blockingBackward
      (P : (L.popularAuxiliaryInput hL.legal).Fragment)
      (blockable : P ∈ GroundingCut.blockableG0
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary)
      (e : V × V)
      (prefix_edge : e ∈ (GroundingBlockingPrefix.data
        (L.popularAuxiliaryInput hL.legal) S.cut P blockable).path.edgeSet)
      (selected_backward : e ∈
        GroundingErasedDecode.erasedSelectedDirectionEdgesAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) ∅ .backward)
  | blockingForwardConflict
      (P : (L.popularAuxiliaryInput hL.legal).Fragment)
      (blockable : P ∈ GroundingCut.blockableG0
        (L.popularAuxiliaryInput hL.legal) S.cut)
      (boundary_eq : GroundingCut.blockingPoint
        (L.popularAuxiliaryInput hL.legal) S.cut P = O.boundary)
      (e : V × V)
      (prefix_edge : e ∈ (GroundingBlockingPrefix.data
        (L.popularAuxiliaryInput hL.legal) S.cut P blockable).path.edgeSet)
      (forward_conflict : e ∈
        GroundingErasedDecode.forwardConflictCutEdgesAt
          (L.popularAuxiliaryIndexed hL) S
          (L.reservedGroundedControls hL S R) ∅)

/-- Every root obstruction admits the backward-normalized classifier. -/
theorem backwardNormalizedRootFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (O : L.Assertion822PreStoppedRootObstruction hL S R) :
    BackwardNormalizedRootFailureOutcome O := by
  cases O.failureOutcome with
  | finite hfinite hcut _p _hchosen _D _hnot _hclass =>
      exact .normalizedFinite
        (O.exists_finiteRootBackwardSwitchData hfinite hcut).some
  | activeControl c heq hactive => exact .activeControl c heq hactive
  | activeRetainedVertex c heq d x hx hnot =>
      exact .activeRetainedVertex c heq d x hx hnot
  | inactiveControl c heq data => exact .inactiveControl c heq data
  | blockingInitial P hP heq hnot =>
      exact .blockingInitial P hP heq hnot
  | blockingBackward P hP heq e hePrefix heBackward =>
      exact .blockingBackward P hP heq e hePrefix heBackward
  | blockingForwardConflict P hP heq e hePrefix heConflict =>
      exact .blockingForwardConflict P hP heq e hePrefix heConflict

end Assertion822PreStoppedRootObstruction

/-- Public compiler in which both finite collision failures and finite root
failures have already been replaced by canonical whole-parent backward
terminal-contact switches. -/
theorem assertion822Output_or_hindrance_of_preStoppedFullyBackwardNormalizedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.BackwardNormalizedRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.BackwardNormalizedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedBackwardNormalizedRepairs
    hL S
  · intro R O _outcome
    exact repairRoot R O O.backwardNormalizedRootFailureOutcome
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.exists_finiteRootBackwardSwitchData
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.FiniteRootBackwardSwitchData.exists_terminalContactWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.FiniteRootBackwardSwitchData.exists_hindrance_of_terminalContactWarp_isWave
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedRootObstruction.backwardNormalizedRootFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedFullyBackwardNormalizedRepairs
