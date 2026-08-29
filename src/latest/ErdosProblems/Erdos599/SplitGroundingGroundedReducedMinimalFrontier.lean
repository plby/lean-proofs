/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReducedSeparator818
import ErdosProblems.Erdos599.GroundingMinimalSeparatingBoundary

/-!
# A minimal frontier inside the source-correct reduced boundary

The corrected Assertion 8.18 permits the simultaneous construction to stop
at an inclusion-minimal separating subset of the reduced boundary.  Every
retained point then has a private ambient source--target path meeting the
frontier only there.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingMinimalSeparatingBoundary

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

theorem exists_splitGroundedReducedMinimalFrontier
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    ∃ T : Set V,
      T ⊆ L.splitGroundedBB hL.legal S.cut ∧
      Popular.IsSeparator Gamma T ∧
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T := by
  apply exists_minimalSeparatingSubset
  exact L.splitGroundedReducedAssertion8_18 hL.legal S.cut S.separates

theorem exists_splitGroundedReducedMinimalFrontier_with_privatePaths
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    ∃ T : Set V,
      T ⊆ L.splitGroundedBB hL.legal S.cut ∧
      Popular.IsSeparator Gamma T ∧
      CardinalInduction.IsMinimalSeparatorFrom Gamma Gamma.source T ∧
      ∀ t ∈ T, ∃ a ∈ Gamma.source,
        ∃ p : DirectedPath.FinitePath Gamma.graph,
          Gamma.IsTargetPathFrom a p ∧ p.support ∩ T = {t} := by
  obtain ⟨T, hTsub, hTsep, hTmin⟩ :=
    L.exists_splitGroundedReducedMinimalFrontier hL hground S
  refine ⟨T, hTsub, hTsep, hTmin, ?_⟩
  intro t ht
  exact exists_privatePath_of_minimalSeparatingSubset hTmin ht

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.exists_splitGroundedReducedMinimalFrontier
#print axioms Erdos599.DWeb.KappaLadder.exists_splitGroundedReducedMinimalFrontier_with_privatePaths
