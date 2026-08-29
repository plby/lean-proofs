/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedTerminalFailureCompiler
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Realizing the successful pre-stopped terminal outcome

The terminal-normalized failure compiler retains the exact finite trace and
its old limiting-ladder terminal.  Once its internal outcome is the
terminal-contact switching branch, arbitrary-ray realization is now
unconditional: cyclic components are discarded and the reverse-ray
obstruction is automatic for a finite perturbation.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedBoundaryObstruction

/-- The switching branch of a canonical private finite outcome realizes a
new arbitrary path/ray warp.  Its initial set loses the contacted ladder
initial, and its terminal frontier loses the finite-source boundary point
at which the exchange started. -/
theorem CanonicalPrivateFiniteTerminalOutcome.exists_terminalContactWarp
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    {D : FirstBoundaryReduction o}
    (data : CanonicalPrivateFiniteTerminalOutcome D)
    (hswitch : IsTerminalContactSwitching
      (L.popularAuxiliaryInput hL.legal).ladder.paths
      data.compression data.terminal) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
        Gamma.initialSet W =
          Gamma.initialSet
              (L.popularAuxiliaryInput hL.legal).ladder.paths \ {data.terminal} ∧
        Gamma.terminalFrontier W =
          Gamma.terminalFrontier
              (L.popularAuxiliaryInput hL.legal).ladder.paths \ {D.reduced.later} := by
  have hinitial : data.compression.initial = D.reduced.later := by
    have h := data.trace.erasedCompression.initial_eq.trans data.trace_initial
    rw [data.compression_eq] at h
    exact h
  obtain ⟨_q, _Q, _y, _hqStart, _hqTarget, _hqAvoid, _hqPrivate,
      _hqPure, _hQInitial, _hQTerminal, _hyTarget, hlaterFrontier,
      _hyInitial, _hnoForward, _hparent, _hback⟩ := data.exchange
  exact TerminalContactSwitch.exists_terminalContactSwitch_anyWarp
    (L.popularAuxiliaryInput hL.legal).ladder.paths
    data.compression data.terminal D.reduced.later hswitch
    hlaterFrontier hinitial

/-- The same realization obtained directly by eliminating the total
terminal outcome.  The two failure alternatives are kept explicit for the
contact-aware decoder normalizer. -/
theorem CanonicalPrivateFiniteTerminalOutcome.switchingWarp_or_failure
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    {D : FirstBoundaryReduction o}
    (data : CanonicalPrivateFiniteTerminalOutcome D) :
    (∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
        Gamma.initialSet W =
          Gamma.initialSet
              (L.popularAuxiliaryInput hL.legal).ladder.paths \ {data.terminal} ∧
        Gamma.terminalFrontier W =
          Gamma.terminalFrontier
              (L.popularAuxiliaryInput hL.legal).ladder.paths \ {D.reduced.later}) ∨
      ¬ ForwardLinksOff
        (L.popularAuxiliaryInput hL.legal).ladder.paths
        (.finite data.compression) ∨
      ¬ PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
        Gamma (L.popularAuxiliaryInput hL.legal).ladder.paths
        (.finite data.compression) := by
  rcases data.terminal_outcome with hswitch | hoff | hcontacts
  · exact Or.inl (data.exists_terminalContactWarp hswitch)
  · exact Or.inr (Or.inl hoff)
  · exact Or.inr (Or.inr hcontacts)

end Assertion822PreStoppedBoundaryObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome.exists_terminalContactWarp
#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome.switchingWarp_or_failure
