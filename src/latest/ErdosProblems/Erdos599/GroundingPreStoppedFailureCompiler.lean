/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedBlockingCollisionReduction
import ErdosProblems.Erdos599.GroundingPreStoppedRootFailureOutcome

/-!
# Compiling the exact pre-stopped failure outcomes

The pre-stopped realization reduces Assertion 8.22 to either a clean output,
an unrooted literal boundary point, or an ordered collision of two literal
boundary points.  The two classifier modules refine the latter alternatives
to finite construction data.  This file is the small public adapter which
lets the remaining exchange argument work directly with those refined
outcomes, without reopening the coarse obstruction structures.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Construction-specific repairs of every refined root and collision
outcome compile to the exact output-or-hindrance disjunction consumed by the
grounding theorem. -/
theorem assertion822Output_or_hindrance_of_preStoppedFailureRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairRoot : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedRootObstruction hL S R),
      O.FailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.FirstBoundaryFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedRepairs' hL S
  · intro R O
    exact repairRoot R O O.failureOutcome
  · intro R O
    exact repairBoundary R O O.firstBoundaryFailureOutcome

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedFailureRepairs
