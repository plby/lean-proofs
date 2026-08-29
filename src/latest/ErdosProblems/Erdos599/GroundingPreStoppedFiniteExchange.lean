/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedBoundaryCollisionCases

/-!
# The finite exchange carried by a pre-stopped boundary collision

The ordered-boundary classifier isolates the mixed case in which the earlier
boundary point is the blocker of a surviving fragment and the later point is
a finite auxiliary source.  If the later point is the terminal of that
fragment, the canonical finite-source compiler does more than produce an
arbitrary decoded alternating path: legality and target-marker freshness make
the loop-erased decode an honest finite trace ending outside the grounded
parent.  This is the exact local exchange datum needed by the remaining
relation-splicing argument.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedBoundaryObstruction

/-- A blocking--finite ordered boundary collision, whose later point is the
terminal of the displayed fragment, supplies a cut-private auxiliary path and
an honest finite alternating exchange trace.  Its target marker is fresh from
the grounded parent of the fragment. -/
theorem exists_private_finite_exchange_of_blocking_finite_terminal
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R)
    (hcase : BlockingFiniteTerminalCase o) :
    ∃ (q : _root_.Erdos599.DirectedPath.FinitePath
          (L.popularAuxiliaryInput hL.legal).lambda.graph)
        (Q : Alternating.FiniteTrace Gamma.graph) (y : V),
      q.start = .old o.later ∧
      q.finish ∈ (L.popularAuxiliaryInput hL.legal).lambda.target ∧
      (L.popularAuxiliaryInput hL.legal).lambda.Avoids q
        (S.cut \ {(.old o.later :
          (L.popularAuxiliaryInput hL.legal).LV)}) ∧
      q.support ∩ S.cut =
        {(.old o.later : (L.popularAuxiliaryInput hL.legal).LV)} ∧
      q.support ∩
        (L.popularAuxiliaryInput hL.legal).lambda.target ⊆ {q.finish} ∧
      (Alternating.AltPath.finite Q).initial = o.later ∧
      (Alternating.AltPath.finite Q).terminal? = some y ∧
      y ∈ (L.popularAuxiliaryInput hL.legal).targetMarkers ∧
      o.later ∈ Gamma.terminalFrontier
        (L.popularAuxiliaryInput hL.legal).ladder.paths ∧
      y ∈ Gamma.initialSet
        (L.popularAuxiliaryInput hL.legal).ladder.paths ∧
      (∀ z, (y, z) ∉
        (Alternating.AltPath.finite Q).directionEdges .forward) ∧
      (∃ P : (L.popularAuxiliaryInput hL.legal).Fragment,
        P ∈ GroundingCut.G0
          (L.popularAuxiliaryInput hL.legal) S.cut ∧
        GroundingCut.blockingPoint
          (L.popularAuxiliaryInput hL.legal) S.cut P = o.earlier ∧
        P.path.terminal? = some o.later ∧
        y ∉ P.parent.support) ∧
      Alternating.BackwardLinksOn
        (L.popularAuxiliaryInput hL.legal).ladder.paths (.finite Q) := by
  obtain ⟨P, hPG0, hblockable, hPearly, hterminal, hlater⟩ := hcase
  obtain ⟨q, Q, y, hqStart, hqTarget, hqAvoid, hqPrivate,
      hqPure, hQInitial, hQTerminal, hyTarget, hyParent, hcFrontier,
      hyInitial, hyNoForward, hback⟩ :=
    L.exists_private_finite_exchange_of_finiteSource_duplicate
      hL.legal S.cut P hPG0.1 hterminal
      (meetsEscape_of_blocking_finite_terminal o hPearly hterminal)
      hlater.1 (GroundingCut.mem_CV.mpr hlater.2) (by
        intro heq
        exact o.distinct (hPearly.symm.trans heq))
  exact ⟨q, Q, y, hqStart, hqTarget, hqAvoid, hqPrivate,
    hqPure, hQInitial, hQTerminal, hyTarget, hcFrontier, hyInitial,
    hyNoForward, ⟨P, hPG0, hPearly, hterminal, hyParent⟩, hback⟩

end Assertion822PreStoppedBoundaryObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.exists_private_finite_exchange_of_blocking_finite_terminal
