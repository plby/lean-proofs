/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFiniteSourceTerminalContact

/-!
# Total internal-geometry outcome for a finite-source exchange

`GroundingFiniteSourceDuplicateExchange` supplies a finite decoded trace
whose backward links lie on the limiting ladder and whose terminal is a
fresh target marker.  Those facts do not by themselves imply the two
maximal-contact hypotheses needed by `TerminalContactSwitch`.

This file gives the lossless boundary between the decoder and the switching
theorem.  A decoded trace either is a terminal-contact switch, or one of the
two exact internal failures is displayed: a forward link uses a ladder
edge, or a nonterminal forward ladder contact is not covered by a backward
link.  For distinct endpoints the trace cannot start forward: contact
coverage would put its ladder initial on a later backward link, contradicting
finite-trace compatibility.  The second alternative is genuinely possible
even under the legality-sensitive finite-source/marker disjointness; see
`GroundingLegalHiddenContactCounterexample`.
-/

noncomputable section

namespace Erdos599
namespace DWeb.KappaLadder

open Set Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The exact unresolved internal geometry of a decoded finite-source
exchange.  Endpoint geometry is deliberately absent: it is discharged
unconditionally by target-marker legality. -/
inductive FiniteSourceTerminalOutcome
    (Z : Set Gamma.DPath) (Q : FiniteTrace Gamma.graph) (y : V) : Prop
  | switching (h : IsTerminalContactSwitching Z Q y)
  | forwardUsesLadderEdge
      (h : ¬ ForwardLinksOff Z (.finite Q))
  | uncoveredForwardContact
      (h : ¬ PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
        Gamma Z (.finite Q))

/-- Backward-link provenance and endpoint legality reduce a finite-source
exchange to the switching case or one of the two literal internal
normalization failures.  No endpoint-preserving normalization is assumed.
-/
theorem finiteSourceTerminalOutcome
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {Q : FiniteTrace Gamma.graph} {y : V}
    (hback : BackwardLinksOn
      (L.popularAuxiliaryInput hlegal).ladder.paths (.finite Q))
    (hinitial : Q.initial ∈ Gamma.vertexSet
      (L.popularAuxiliaryInput hlegal).ladder.paths)
    (hne : Q.initial ≠ y)
    (hterminal : Q.terminal = y)
    (hyTarget : y ∈
      (L.popularAuxiliaryInput hlegal).targetMarkers)
    (hnoForward : ∀ z,
      (y, z) ∉ (AltPath.finite Q).directionEdges .forward) :
    FiniteSourceTerminalOutcome
      (L.popularAuxiliaryInput hlegal).ladder.paths Q y := by
  classical
  let Z := (L.popularAuxiliaryInput hlegal).ladder.paths
  by_cases hoff : ForwardLinksOff Z (.finite Q)
  · by_cases hcontacts :
        PopularAuxiliary.Input.ForwardVertexContactsCoveredAtTerminal
          Gamma Z (.finite Q)
    · apply FiniteSourceTerminalOutcome.switching
      exact L.terminalContactSwitching_of_targetMarker_of_distinct hlegal
        (L.popularAuxiliaryInput hlegal).ladder.2 hback hoff hcontacts
        hinitial hne hterminal hyTarget hnoForward
    · exact .uncoveredForwardContact hcontacts
  · exact .forwardUsesLadderEdge hoff

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.finiteSourceTerminalOutcome
