/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedFiniteRootBackwardSwitch

/-!
# Wave endpoint of the canonical finite-source backward switch

The canonical backward normalization removes a genuine original source from
the switched family's initial set.  Hence showing that its realized family is
a wave is the only remaining condition needed to obtain a hindrance.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace Assertion822PreStoppedBoundaryObstruction

/-- Once the canonical normalized realization is a wave, deletion of its
grounded-parent source makes it a hindrance. -/
theorem CanonicalPrivateFiniteTerminalOutcome.exists_hindrance_of_normalizedTerminalContactWarp_isWave
    {L : Gamma.KappaLadder kappa} {hL : L.IsKappaHindrance}
    {S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)}
    {R : L.UnusedGroundedRecord hL S}
    {o : L.Assertion822PreStoppedBoundaryObstruction hL S R}
    {D : FirstBoundaryReduction o}
    (data : CanonicalPrivateFiniteTerminalOutcome D)
    (wave : ∀ (u : V) (W : Set Gamma.DPath),
      u ∈ Gamma.initialSet
        (L.popularAuxiliaryInput hL.legal).ladder.paths →
      u ∈ Gamma.source →
      Gamma.IsWarp W →
      Gamma.initialSet W =
        Gamma.initialSet
          (L.popularAuxiliaryInput hL.legal).ladder.paths \ {u} →
      Gamma.terminalFrontier W =
        Gamma.terminalFrontier
          (L.popularAuxiliaryInput hL.legal).ladder.paths \
            {D.reduced.later} →
      Gamma.IsWave W) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  obtain ⟨u, W, huInitial, huSource, hwarp, hinitial, hterminal⟩ :=
    data.exists_normalizedTerminalContactWarp
  refine ⟨W,
    wave u W huInitial huSource hwarp hinitial hterminal, ?_⟩
  intro heq
  have huW : u ∈ Gamma.initialSet W := heq.symm ▸ huSource
  rw [hinitial] at huW
  exact huW.2 rfl

end Assertion822PreStoppedBoundaryObstruction
end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Assertion822PreStoppedBoundaryObstruction.CanonicalPrivateFiniteTerminalOutcome.exists_hindrance_of_normalizedTerminalContactWarp_isWave
