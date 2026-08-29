/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReachableBoundaryNormal

/-!
# Normalized public outcome for the grounded split separator branch

This is the public source-reachable dispatcher with its ordered-boundary
branch expanded to first-hit source geometry, exact endpoint owners, the
finite-source sink reduction, and the first selected-forward decomposition.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

/-- Exact normalized outcome of the canonical grounded switch. -/
theorem splitGroundedCanonicalAssertion822Output_or_normalizedReachableObstruction
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) ∨
      Nonempty (L.SplitGroundedReachableReservedRootObstruction
        (L.splitGroundedCanonicalUnusedRecord hL hground S)) ∨
      Nonempty (L.SplitGroundedReachableWholeSourceRootObstruction
        (L.splitGroundedCanonicalUnusedRecord hL hground S)) ∨
      ∃ O : L.SplitGroundedReachableBoundaryObstruction
          (L.splitGroundedCanonicalUnusedRecord hL hground S),
        SplitGroundedReachableFirstBoundarySinkOutcome O := by
  rcases L.splitGroundedCanonicalAssertion822Output_or_reachableObstruction
      hL hground S with houtput | hreserved | hwhole | hboundary
  · exact Or.inl houtput
  · exact Or.inr (Or.inl hreserved)
  · exact Or.inr (Or.inr (Or.inl hwhole))
  · obtain ⟨O⟩ := hboundary
    exact Or.inr (Or.inr (Or.inr ⟨O, O.firstBoundarySinkOutcome⟩))

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedCanonicalAssertion822Output_or_normalizedReachableObstruction
