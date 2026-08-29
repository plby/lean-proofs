/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedBoundaryFiniteExchange
import ErdosProblems.Erdos599.TerminalContactSwitchGeometry

/-!
# Split-legal terminal normalization of the private finite exchange

The private blocker--finite exchange is normalized against the actual
limiting warp.  This is the split-legal replacement for the legacy
`finiteSourceTerminalOutcome`: no ordinary-legality witness is introduced.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev FiniteTerminalInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

/-- The private finite exchange has a total, geometry-only terminal-contact
outcome against the genuine limiting warp. -/
theorem SplitGroundedBlockingFiniteTerminalCase.exists_terminalContactGeometryOutcome
    {R : L.SplitGroundedUnusedRecord hL hground S K}
    {O : L.SplitGroundedPreStoppedBoundaryObstruction R}
    (hcase : SplitGroundedBlockingFiniteTerminalCase O) :
    ∃ (Q : FiniteTrace Gamma.graph) (y : V),
      Q.initial = O.later ∧
      Q.terminal = y ∧
      y ∈ (FiniteTerminalInput (L := L) (hL := hL)).targetMarkers ∧
      O.later ∈ Gamma.terminalFrontier
        (FiniteTerminalInput (L := L) (hL := hL)).ladder.paths ∧
      TerminalContactGeometryOutcome
        (FiniteTerminalInput (L := L) (hL := hL)).ladder.paths Q y := by
  obtain ⟨P, q, Q, y, _hPG0, hPterminal, _hqStart, _hqTarget,
      _hqAvoid, _hqPrivate, _hqPure, hQInitial, hQTerminal, hyTarget,
      hyParent, hlaterFrontier, hyInitial, hnoForward, hback⟩ :=
    hcase.exists_private_finite_exchange
  have hQi : Q.initial = O.later := by
    change Q.initial = O.later at hQInitial
    exact hQInitial
  have hQt : Q.terminal = y := by
    simpa only [AltPath.terminal?_finite, Option.some.injEq] using hQTerminal
  have hinitial : Q.initial ∈ Gamma.vertexSet
      (FiniteTerminalInput (L := L) (hL := hL)).ladder.paths := by
    rw [hQi]
    exact terminalFrontier_subset_vertexSet _ hlaterFrontier
  have hne : Q.initial ≠ y := by
    rw [hQi]
    intro heq
    apply hyParent
    exact heq ▸ P.support_subset
      (Gamma.terminal_mem_support hPterminal)
  have hwarp : Gamma.IsWarp
      (FiniteTerminalInput (L := L) (hL := hL)).ladder.paths := by
    simpa [FiniteTerminalInput, splitGroundedPopularAuxiliaryInput,
      KappaLadder.limitWarp]
      using hL.legal.warpStages (Ladder.finalStage kappa)
  refine ⟨Q, y, hQi, hQt, hyTarget, hlaterFrontier, ?_⟩
  exact finiteSourceTerminalOutcome_of_geometry hwarp hback hinitial
    hyInitial hne hQt hnoForward

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.SplitGroundedBlockingFiniteTerminalCase.exists_terminalContactGeometryOutcome
