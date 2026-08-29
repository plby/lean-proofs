/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedSeparatorGeometry
import ErdosProblems.Erdos599.SplitGroundingGroundedSeparator818
import ErdosProblems.Erdos599.GroundingMinimalSeparatingBoundary

/-!
# A minimal separating frontier inside the split-grounded boundary

Assertion 8.18 is first proved for the literal boundary `BB`.  That set can
contain two points on one limiting-ladder component, so it is not the right
terminal set for the simultaneous switch.  This module performs the exact
source-level normalization: choose an inclusion-minimal ambient separator
inside `BB`.  Each retained point then has a private original-source--target
path meeting the chosen frontier only there.

No conversion from split legality to the legacy legality predicate is used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingMinimalSeparatingBoundary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

/-- A split-grounded auxiliary separator has an inclusion-minimal ambient
separating sub-frontier inside its Assertion 8.18 boundary. -/
theorem exists_splitGroundedMinimalFrontier
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    ∃ T : Set V,
      T ⊆ GroundingCut.BB
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut ∧
      Popular.IsSeparator Gamma T ∧
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T := by
  apply exists_minimalSeparatingSubset
  exact L.splitGroundedAssertion8_18 hL.legal S.cut S.separates

/-- Witness form of the same construction.  The private path is the exact
ambient source geometry used to normalize a retained boundary collision. -/
theorem exists_splitGroundedMinimalFrontier_with_privatePaths
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    ∃ T : Set V,
      T ⊆ GroundingCut.BB
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut ∧
      Popular.IsSeparator Gamma T ∧
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T ∧
      ∀ t ∈ T, ∃ a ∈ Gamma.source,
        ∃ p : DirectedPath.FinitePath Gamma.graph,
          Gamma.IsTargetPathFrom a p ∧ p.support ∩ T = {t} := by
  obtain ⟨T, hTsub, hTsep, hTmin⟩ :=
    L.exists_splitGroundedMinimalFrontier hL hground S
  refine ⟨T, hTsub, hTsep, hTmin, ?_⟩
  intro t ht
  exact exists_privatePath_of_minimalSeparatingSubset hTmin ht

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.exists_splitGroundedMinimalFrontier
#print axioms Erdos599.DWeb.KappaLadder.exists_splitGroundedMinimalFrontier_with_privatePaths
