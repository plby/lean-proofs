/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingTheorem
import ErdosProblems.Erdos599.GroundingPreStoppedFiniteRootBackwardSwitch

/-!
# Final grounding interface with normalized finite collisions

This is the strongest source-faithful public assembly currently available.
The stationary equal branch remains explicit.  In the separator branch the
private blocking--finite collision is already normalized to the canonical
whole-parent backward terminal-contact switch; consumers no longer receive
the false raw-erasure contact obligations.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The construction-specific separator repairs which remain after the
private finite collision has been normalized to the whole-parent backward
switch. -/
structure NormalizedPreStoppedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) where
  root : ∀
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (o : L.Assertion822PreStoppedRootObstruction hL S R),
    o.BackwardNormalizedRootFailureOutcome →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W
  boundary : ∀
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (R : L.UnusedGroundedRecord hL S)
    (o : L.Assertion822PreStoppedBoundaryObstruction hL S R),
    o.BackwardNormalizedTerminalFailureOutcome →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W

/-- Combine target-pure equal grounding with the total pre-stopped failure
compiler after canonical finite-parent normalization. -/
theorem exists_hindrance_of_targetPureEqualGrounding_and_normalizedPreStoppedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (equalGrounding : ∀
      (P : Popular.XSWarp
        (L.popularAuxiliaryInput hL.legal).lambda
        (L.popularAuxiliaryInput hL.legal).lambda.target),
      (∀ p (hp : p ∈ P.paths),
        (L.popularAuxiliaryInput hL.legal).IsTargetPure p) →
      Stationary.IsStationaryBelow kappa
        (Popular.initialIndicesOf (L.popularAuxiliaryIndexed hL)
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).paths
          ((L.popularAuxiliaryIndexed hL).equalSubwarp P).starts_in_source) →
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairs : NormalizedPreStoppedRepairs L hL) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.exists_hindrance_of_targetPureEqualGrounding_and_assertion822_or_hindrance
    hL equalGrounding
  intro S
  exact L.assertion822Output_or_hindrance_of_preStoppedFullyBackwardNormalizedRepairs
    hL S (repairs.root S) (repairs.boundary S)

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_of_targetPureEqualGrounding_and_normalizedPreStoppedRepairs
