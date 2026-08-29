/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedCanonicalReachableDefects
import ErdosProblems.Erdos599.SplitGroundingGroundedReachableBoundaryFinite

/-!
# Canonical finite-normalized defects of the grounded split switch

This combines the source-faithful root-defect dispatcher with the exact
finite-terminal normalization of the ordered boundary branch.  Thus the
last alternative no longer contains the coarse blocker-to-finite owner
pair: it records either the residual fragment-terminal collision or the
first selected active departure at the blocker.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

/-- Fully concrete canonical dispatcher with the ordered boundary branch
reduced to its exact finite-terminal/departure normal form. -/
theorem splitGroundedCanonicalAssertion822Output_or_finiteReachableDefect
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) ∨
      (∃ O : L.SplitGroundedReachableEssentialReservedRootObstruction
          (hL := hL) (hground := hground) (S := S),
        L.SplitGroundedEssentialReservedAmbientDefectOutcome O) ∨
      (∃ O : L.SplitGroundedReachableWholeSourceRootObstruction
          (L.splitGroundedCanonicalUnusedRecord hL hground S),
        ∃ data : L.SplitGroundedWholeSourceAmbientLastDeletedHeadData O,
          L.SplitGroundedWholeSourceAmbientDeletedHeadOutcome O data) ∨
      (∃ O : L.SplitGroundedReachableBoundaryObstruction
          (L.splitGroundedCanonicalUnusedRecord hL hground S),
        SplitGroundedReachableBoundaryFiniteOutcome O) := by
  rcases L.splitGroundedCanonicalAssertion822Output_or_concreteReachableDefect
      hL hground S with houtput | hessential | hwhole | hboundary
  · exact Or.inl houtput
  · exact Or.inr (Or.inl hessential)
  · exact Or.inr (Or.inr (Or.inl hwhole))
  · right
    right
    right
    obtain ⟨O, _⟩ := hboundary
    exact ⟨O, O.boundaryFiniteOutcome⟩

/-- Hindrance-valued form of the same lossless dispatcher.  The successful
Assertion 8.22 branch is consumed immediately; every remaining alternative
retains its exact source-faithful exchange data. -/
theorem exists_hindrance_or_splitGroundedCanonicalFiniteReachableDefect
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    (∃ W : Set Gamma.DPath, Gamma.IsHindrance W) ∨
      (∃ O : L.SplitGroundedReachableEssentialReservedRootObstruction
          (hL := hL) (hground := hground) (S := S),
        L.SplitGroundedEssentialReservedAmbientDefectOutcome O) ∨
      (∃ O : L.SplitGroundedReachableWholeSourceRootObstruction
          (L.splitGroundedCanonicalUnusedRecord hL hground S),
        ∃ data : L.SplitGroundedWholeSourceAmbientLastDeletedHeadData O,
          L.SplitGroundedWholeSourceAmbientDeletedHeadOutcome O data) ∨
      (∃ O : L.SplitGroundedReachableBoundaryObstruction
          (L.splitGroundedCanonicalUnusedRecord hL hground S),
        SplitGroundedReachableBoundaryFiniteOutcome O) := by
  rcases L.splitGroundedCanonicalAssertion822Output_or_finiteReachableDefect
      hL hground S with houtput | hessential | hwhole | hboundary
  · exact Or.inl
      (exists_hindrance_of_splitGroundedAssertion822Output houtput.some)
  · exact Or.inr (Or.inl hessential)
  · exact Or.inr (Or.inr (Or.inl hwhole))
  · exact Or.inr (Or.inr (Or.inr hboundary))

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedCanonicalAssertion822Output_or_finiteReachableDefect
#print axioms
  Erdos599.DWeb.KappaLadder.exists_hindrance_or_splitGroundedCanonicalFiniteReachableDefect
