/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteSourceBackwardSwitch

/-!
# Casewise compiler for pre-stopped Assertion 8.22 failures

The terminal-normalized failure compiler deliberately retains a total
dependent outcome.  This file exposes its eliminator in the form needed by
the construction-specific exchange argument.  In particular, the private
finite collision is no longer a single undifferentiated callback: it is
split into the
successful terminal switch, a literal forward ladder step in the decoder,
or one uncovered forward contact.

No geometric conclusion is added here.  The theorem only prevents later
integration code from reopening the nested first-boundary and decoder
classifications, and makes the exact remaining repair obligations visible
in its type.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A private finite collision is repaired once its three exhaustive
normalization outcomes are repaired. -/
theorem
    Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome.exists_hindrance_of_normalizationRepairs
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {O : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    {D : O.FirstBoundaryReduction}
    (data : Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome D)
    (repairSwitching : IsTerminalContactSwitching
        (L.popularAuxiliaryInput hL.legal).ladder.paths
          data.compression data.terminal →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairForwardLadderStep : ∀
        (s : PopularAuxiliary.Input.SignedEdge V),
      s ∈ data.trace.runs.erasedSignedRoute.steps →
      s.direction = .forward →
      s.edge ∈ Alternating.familyEdges
        (L.popularAuxiliaryInput hL.legal).ladder.paths →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairUncoveredContact : ∀ x,
      x ∈ (AltPath.finite data.compression).directionVertices .forward →
      x ∈ Gamma.vertexSet
        (L.popularAuxiliaryInput hL.legal).ladder.paths →
      x ∉ (AltPath.finite data.compression).directionVertices .backward →
      (AltPath.finite data.compression).terminal? ≠ some x →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  cases data.normalizationOutcome with
  | switching h => exact repairSwitching h
  | forwardLadderStep s hs hd he =>
      exact repairForwardLadderStep s hs hd he
  | uncoveredContact x hforward hladder hnotBackward hnotTerminal =>
      exact repairUncoveredContact x hforward hladder hnotBackward
        hnotTerminal

/-- Casewise form of the terminal-normalized Assertion 8.22 compiler.

The root obstruction remains in its already-lossless `FailureOutcome`
normal form.  Every collision obstruction is split into the five coarse
first-boundary alternatives, with the private finite alternative further
split into the three literal decoder outcomes above. -/
theorem assertion822Output_or_hindrance_of_preStoppedNormalizedCaseRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.FailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairEarlierFinite : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction),
      Assertion822PreStoppedBoundaryObstruction.FiniteCase
          hL S D.reduced.earlier →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairEarlierControl : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction),
      Assertion822PreStoppedBoundaryObstruction.ControlCase
          hL S D.reduced.earlier →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairPrivateSwitching : ∀
        (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction)
        (data : Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome D),
      IsTerminalContactSwitching
        (L.popularAuxiliaryInput hL.legal).ladder.paths
          data.compression data.terminal →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairPrivateForwardLadderStep : ∀
        (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction)
        (data : Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome D)
        (s : PopularAuxiliary.Input.SignedEdge V),
      s ∈ data.trace.runs.erasedSignedRoute.steps →
      s.direction = .forward →
      s.edge ∈ Alternating.familyEdges
        (L.popularAuxiliaryInput hL.legal).ladder.paths →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairPrivateUncoveredContact : ∀
        (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction)
        (data : Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome D) (x : V),
      x ∈ (AltPath.finite data.compression).directionVertices .forward →
      x ∈ Gamma.vertexSet
        (L.popularAuxiliaryInput hL.legal).ladder.paths →
      x ∉ (AltPath.finite data.compression).directionVertices .backward →
      (AltPath.finite data.compression).terminal? ≠ some x →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairSelectedDeparture : ∀
        (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction),
      Assertion822PreStoppedBoundaryObstruction.FirstSelectedDeparture D →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBlockingToControl : ∀
        (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction),
      Assertion822PreStoppedBoundaryObstruction.BlockingCase
          hL S D.reduced.earlier →
      Assertion822PreStoppedBoundaryObstruction.ControlCase
          hL S D.reduced.later →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBlockingToBlocking : ∀
        (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction),
      Assertion822PreStoppedBoundaryObstruction.BlockingCase
          hL S D.reduced.earlier →
      Assertion822PreStoppedBoundaryObstruction.BlockingCase
          hL S D.reduced.later →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedTerminalFailureRepairs
    hL S repairRoot
  intro R O outcome
  cases outcome with
  | earlierFinite D hfinite =>
      exact repairEarlierFinite R O D hfinite
  | earlierControl D hcontrol =>
      exact repairEarlierControl R O D hcontrol
  | privateFinite D data =>
      exact data.exists_hindrance_of_normalizationRepairs
        (repairPrivateSwitching R O D data)
        (repairPrivateForwardLadderStep R O D data)
        (repairPrivateUncoveredContact R O D data)
  | selectedDeparture D hdeparture =>
      exact repairSelectedDeparture R O D hdeparture
  | blockingToControl D hblocking hcontrol =>
      exact repairBlockingToControl R O D hblocking hcontrol
  | blockingToBlocking D hearlier hlater =>
      exact repairBlockingToBlocking R O D hearlier hlater

/-- Stronger casewise compiler using the canonical parent-backward
normalization in the private finite branch.  The two raw decoder failure
callbacks disappear: every private finite collision supplies one honest
terminal-contact switch, independently of the chronologically erased
auxiliary trace. -/
theorem assertion822Output_or_hindrance_of_preStoppedBackwardSwitchRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.FailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairEarlierFinite : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction),
      Assertion822PreStoppedBoundaryObstruction.FiniteCase
          hL S D.reduced.earlier →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairEarlierControl : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction),
      Assertion822PreStoppedBoundaryObstruction.ControlCase
          hL S D.reduced.earlier →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairPrivateNormalizedSwitch : ∀
        (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction)
        (data : Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome D)
        (Q : FiniteTrace Gamma.graph) (u : V),
      IsTerminalContactSwitching
          (L.popularAuxiliaryInput hL.legal).ladder.paths Q u →
      Q.initial = D.reduced.later →
      u ∈ Gamma.initialSet
          (L.popularAuxiliaryInput hL.legal).ladder.paths →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairSelectedDeparture : ∀
        (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction),
      Assertion822PreStoppedBoundaryObstruction.FirstSelectedDeparture D →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBlockingToControl : ∀
        (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction),
      Assertion822PreStoppedBoundaryObstruction.BlockingCase
          hL S D.reduced.earlier →
      Assertion822PreStoppedBoundaryObstruction.ControlCase
          hL S D.reduced.later →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBlockingToBlocking : ∀
        (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R)
        (D : O.FirstBoundaryReduction),
      Assertion822PreStoppedBoundaryObstruction.BlockingCase
          hL S D.reduced.earlier →
      Assertion822PreStoppedBoundaryObstruction.BlockingCase
          hL S D.reduced.later →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedTerminalFailureRepairs
    hL S repairRoot
  intro R O outcome
  cases outcome with
  | earlierFinite D hfinite =>
      exact repairEarlierFinite R O D hfinite
  | earlierControl D hcontrol =>
      exact repairEarlierControl R O D hcontrol
  | privateFinite D data =>
      exact data.exists_hindrance_of_normalizedTerminalContactRepair
        (repairPrivateNormalizedSwitch R O D data)
  | selectedDeparture D hdeparture =>
      exact repairSelectedDeparture R O D hdeparture
  | blockingToControl D hblocking hcontrol =>
      exact repairBlockingToControl R O D hblocking hcontrol
  | blockingToBlocking D hearlier hlater =>
      exact repairBlockingToBlocking R O D hearlier hlater

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome.exists_hindrance_of_normalizationRepairs
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedNormalizedCaseRepairs
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedBackwardSwitchRepairs
