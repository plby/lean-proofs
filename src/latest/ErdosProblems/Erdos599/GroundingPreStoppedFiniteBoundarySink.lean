/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteSourceBoundary
import ErdosProblems.Erdos599.GroundingPreStoppedParentInitialRootOutcome

/-!
# Eliminating a finite source as the first pre-stopped boundary

The finite-source sink argument is independent of the chosen controls.  It
therefore applies to the reserved selector used by the pre-stopped compiler.
Consequently a nontrivial directed boundary collision cannot start at a
finite auxiliary source.  This removes the `earlierFinite` constructor from
the normalized boundary obstruction.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating GroundingErasedDecode
open GroundingForwardTailClassification GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- No selected forward edge in the pre-stopped relation can leave a finite
source which is itself represented in the cut.  The proof is uniform in the
selector controls. -/
theorem finiteSource_noOutgoing_directionEdgesAt_empty_of_mem_cut
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (K : GroundingSelection.Controls S)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut) :
    ¬ HasOutgoing
      (erasedSelectedDirectionEdgesAt (L.popularAuxiliaryIndexed hL)
        S K ∅ .forward) b := by
  intro hout
  have hbCV : b ∈ GroundingCut.CV
      (L.popularAuxiliaryInput hL.legal) S.cut :=
    GroundingCut.mem_CV.mpr hbCut
  obtain ⟨y, hby⟩ := hout
  simp only [erasedSelectedDirectionEdgesAt, Set.mem_iUnion] at hby
  obtain ⟨c, hby⟩ := hby
  rcases selectedForwardTail_at_CV_edge_or_startingProxy
      (L.popularAuxiliaryIndexed hL) S K (chosenRequest c.1)
        hbCV hby with
    ⟨v, d, hvd⟩ | ⟨i, d, _hstart, _hid, hbi⟩
  · let q := strongSelectedPath (L.popularAuxiliaryIndexed hL) S K
      (chosenRequest c.1)
    have hqStart : q.start ∈
        (L.popularAuxiliaryInput hL.legal).lambda.source :=
      (strongSelectedWarp (L.popularAuxiliaryIndexed hL) S K).starts_in_source
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

/-- A finite cut source is a sink of the reserved pre-stopped relation. -/
theorem finiteSource_noOutgoing_reservedPreStopped_of_mem_cut
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    {b : V}
    (hb : b ∈ (L.popularAuxiliaryInput hL.legal).finiteSource)
    (hbCut : PopularAuxiliary.Input.LambdaVertex.old b ∈ S.cut) :
    ¬ HasOutgoing (L.assertion822ReservedPreStoppedEdges hL S R) b := by
  intro hout
  obtain ⟨y, hby⟩ := hout
  change (b, y) ∈ erasedSelectedSwitchedEdgesAt
    (L.popularAuxiliaryIndexed hL) S
      (L.reservedGroundedControls hL S R) ∅ at hby
  rw [erasedSelectedSwitchedEdgesAt_empty_eq] at hby
  rcases hby with hresidual | hforward
  · exact L.finiteSource_noOutgoing_residualLadderEdges hL S hb
      ⟨y, hresidual.1⟩
  · exact L.finiteSource_noOutgoing_directionEdgesAt_empty_of_mem_cut
      hL S (L.reservedGroundedControls hL S R) hb hbCut ⟨y, hforward⟩

namespace Assertion822PreStoppedBoundaryObstruction

/-- Boundary failures after eliminating the impossible finite-source first
endpoint. -/
inductive FiniteSinkReducedTerminalFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) : Prop
  | earlierControl
      (D : FirstBoundaryReduction o)
      (earlier : ControlCase hL S D.reduced.earlier)
  | normalizedPrivateFinite
      (D : FirstBoundaryReduction o)
      (data : CanonicalPrivateFiniteTerminalOutcome D)
      (Q : FiniteTrace Gamma.graph) (u : V)
      (switching : IsTerminalContactSwitching
        (L.popularAuxiliaryInput hL.legal).ladder.paths Q u)
      (initial : Q.initial = D.reduced.later)
      (terminal_initial : u ∈ Gamma.initialSet
        (L.popularAuxiliaryInput hL.legal).ladder.paths)
      (terminal_source : u ∈ Gamma.source)
  | selectedDeparture
      (D : FirstBoundaryReduction o)
      (departure : FirstSelectedDeparture D)
  | blockingToControl
      (D : FirstBoundaryReduction o)
      (earlier : BlockingCase hL S D.reduced.earlier)
      (later : ControlCase hL S D.reduced.later)
  | blockingToBlocking
      (D : FirstBoundaryReduction o)
      (earlier : BlockingCase hL S D.reduced.earlier)
      (later : BlockingCase hL S D.reduced.later)

/-- The finite-source first endpoint contradicts the nontrivial reachability
carried by the first-boundary reduction. -/
theorem finiteSinkReducedTerminalFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) :
    FiniteSinkReducedTerminalFailureOutcome o := by
  cases o.backwardNormalizedTerminalFailureOutcome with
  | earlierFinite D hearlier =>
      have heq := GroundingErasedEndpointBoundary.eq_of_reflTransGen_of_noOutgoing
        (L.finiteSource_noOutgoing_reservedPreStopped_of_mem_cut
          hL S R hearlier.1 hearlier.2)
        D.reduced.reaches
      exact False.elim (D.reduced.distinct heq)
  | earlierControl D hearlier => exact .earlierControl D hearlier
  | normalizedPrivateFinite D data Q u hswitch hinitial huInitial huSource =>
      exact .normalizedPrivateFinite D data Q u hswitch hinitial huInitial huSource
  | selectedDeparture D hdeparture =>
      exact .selectedDeparture D hdeparture
  | blockingToControl D hearlier hlater =>
      exact .blockingToControl D hearlier hlater
  | blockingToBlocking D hearlier hlater =>
      exact .blockingToBlocking D hearlier hlater

end Assertion822PreStoppedBoundaryObstruction

/-- Pre-stopped compiler with both the root recursion and the finite-source
first-boundary case normalized. -/
theorem assertion822Output_or_hindrance_of_preStoppedFiniteSinkRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.ParentInitialRecursiveRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.FiniteSinkReducedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedParentInitialRootRepairs
    hL S repairRoot
  intro R O _outcome
  exact repairBoundary R O O.finiteSinkReducedTerminalFailureOutcome

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.finiteSource_noOutgoing_reservedPreStopped_of_mem_cut
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.finiteSinkReducedTerminalFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedFiniteSinkRepairs
