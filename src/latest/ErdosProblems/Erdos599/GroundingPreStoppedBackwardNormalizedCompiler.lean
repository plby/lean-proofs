/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteSourceBackwardSwitch

/-!
# Pre-stopped compiler with the finite collision normalized

The private finite constructor no longer exposes the two erased-decoder
failures.  It carries the canonical whole-parent backward terminal-contact
switch.  All other pre-stopped obstruction constructors remain lossless.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedBoundaryObstruction

/-- Total pre-stopped boundary outcome after replacing a finite duplicate by
the canonical backward switch along its grounded parent. -/
inductive BackwardNormalizedTerminalFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) : Prop
  | earlierFinite
      (D : FirstBoundaryReduction o)
      (earlier : FiniteCase hL S D.reduced.earlier)
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

/-- Every pre-stopped boundary obstruction has a total outcome in which the
private finite collision is already terminal-contact normalized. -/
theorem backwardNormalizedTerminalFailureOutcome
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R) :
    BackwardNormalizedTerminalFailureOutcome o := by
  cases o.terminalFailureOutcome with
  | earlierFinite D hfinite => exact .earlierFinite D hfinite
  | earlierControl D hcontrol => exact .earlierControl D hcontrol
  | privateFinite D data =>
      obtain ⟨Q, u, hswitch, hQinitial, huInitial, huSource⟩ :=
        data.exists_normalizedTerminalContactSwitching
      exact .normalizedPrivateFinite D data Q u hswitch hQinitial huInitial huSource
  | selectedDeparture D hdeparture =>
      exact .selectedDeparture D hdeparture
  | blockingToControl D hearlier hlater =>
      exact .blockingToControl D hearlier hlater
  | blockingToBlocking D hearlier hlater =>
      exact .blockingToBlocking D hearlier hlater

end Assertion822PreStoppedBoundaryObstruction

/-- Pre-stopped Assertion 8.22 compiler with a single, already-normalized
private finite callback.  In particular no callback for a raw forward
ladder step or an uncovered erased contact remains. -/
theorem assertion822Output_or_hindrance_of_preStoppedBackwardNormalizedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.FailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.BackwardNormalizedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedTerminalFailureRepairs
    hL S repairRoot
  intro R O _outcome
  exact repairBoundary R O O.backwardNormalizedTerminalFailureOutcome

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.backwardNormalizedTerminalFailureOutcome
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedBackwardNormalizedRepairs
