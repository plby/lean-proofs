/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedInessentialBoundaryReduction
import ErdosProblems.Erdos599.GroundingPreStoppedBackwardSelfNormalizedOutcome
import ErdosProblems.Erdos599.GroundingPreStoppedWholeSourceRootClassification

/-!
# Essential-root reduction with self-backward normalization

This is the common public seam of the two independent sound reductions:
nonessential fully rooted boundaries are compiled directly into Assertion
8.22, while an essential reserved-source obstruction is passed through the
well-founded self-backward normalizer before reaching its repair callback.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Pre-stopped compiler combining the full-source/nonessential-boundary
reduction with total self-backward normalization of the remaining essential
reserved-source root obstruction. -/
theorem
    assertion822Output_or_hindrance_of_preStoppedEssentialBackwardSelfNormalizedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairEssential : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822EssentialReservedRootObstruction hL S R),
      O.obstruction.BackwardSelfNormalizedFirstFragmentRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairWholeSource : ∀ (R : L.UnusedGroundedRecord hL S),
      L.Assertion822WholeSourceRootObstruction hL S R →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.FiniteSinkReducedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply L.assertion822Output_or_hindrance_of_preStoppedEssentialRepairs
    hL S
  · intro R O _outcome
    exact repairEssential R O
      O.obstruction.backwardSelfNormalizedFirstFragmentRootFailureOutcome
  · exact repairWholeSource
  · exact repairBoundary

/-- Sharpen the whole-source callback as well: both kinds of root failure now
arrive with the same well-founded self-backward-normalized classification,
while the whole-source branch retains its stronger non-reachability proof. -/
theorem
    assertion822Output_or_hindrance_of_preStoppedEssentialWholeSourceClassifiedRepairs
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (repairEssential : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822EssentialReservedRootObstruction hL S R),
      O.obstruction.BackwardSelfNormalizedFirstFragmentRootFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairWholeSource : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822WholeSourceRootObstruction hL S R),
      O.BackwardSelfNormalizedClassification →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W)
    (repairBoundary : ∀ (R : L.UnusedGroundedRecord hL S)
        (O : L.Assertion822PreStoppedBoundaryObstruction hL S R),
      O.FiniteSinkReducedTerminalFailureOutcome →
        ∃ W : Set Gamma.DPath, Gamma.IsHindrance W) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.popularAuxiliaryInput hL.legal) S.cut) ∨
      ∃ W : Set Gamma.DPath, Gamma.IsHindrance W := by
  apply
    L.assertion822Output_or_hindrance_of_preStoppedEssentialBackwardSelfNormalizedRepairs
      hL S repairEssential
  · intro R O
    exact repairWholeSource R O O.backwardSelfNormalizedClassification
  · exact repairBoundary

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedEssentialBackwardSelfNormalizedRepairs
#print axioms
  Erdos599.DWeb.KappaLadder.assertion822Output_or_hindrance_of_preStoppedEssentialWholeSourceClassifiedRepairs
