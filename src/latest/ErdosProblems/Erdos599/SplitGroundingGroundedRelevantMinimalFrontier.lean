/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedRelevantSeparator818
import ErdosProblems.Erdos599.GroundingMinimalSeparatingBoundary

/-!
# A minimal frontier inside the descent-relevant boundary
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingMinimalSeparatingBoundary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

theorem exists_splitGroundedRelevantMinimalFrontier
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    ∃ T : Set V,
      T ⊆ L.splitGroundedRelevantBB hL.legal S.cut ∧
      Popular.IsSeparator Gamma T ∧
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T := by
  apply exists_minimalSeparatingSubset
  exact L.splitGroundedRelevantAssertion8_18 hL.legal S.cut S.separates

theorem exists_splitGroundedRelevantMinimalFrontier_with_privatePaths
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    ∃ T : Set V,
      T ⊆ L.splitGroundedRelevantBB hL.legal S.cut ∧
      Popular.IsSeparator Gamma T ∧
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T ∧
      ∀ t ∈ T, ∃ a ∈ Gamma.source,
        ∃ p : DirectedPath.FinitePath Gamma.graph,
          Gamma.IsTargetPathFrom a p ∧ p.support ∩ T = {t} := by
  obtain ⟨T, hTsub, hTsep, hTmin⟩ :=
    L.exists_splitGroundedRelevantMinimalFrontier hL hground S
  refine ⟨T, hTsub, hTsep, hTmin, ?_⟩
  intro t ht
  exact exists_privatePath_of_minimalSeparatingSubset hTmin ht

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.exists_splitGroundedRelevantMinimalFrontier
#print axioms Erdos599.DWeb.KappaLadder.exists_splitGroundedRelevantMinimalFrontier_with_privatePaths

