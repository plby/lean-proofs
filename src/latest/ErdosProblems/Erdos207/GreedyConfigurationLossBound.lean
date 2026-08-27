/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyConfigurationLossSelectors
import ErdosProblems.Erdos207.GreedyConfigurationCardinality
import ErdosProblems.Erdos207.RestrictedThreatUnionDeviation

/-! # Configuration loss coefficient and its explicit overlap error -/

namespace Erdos207

open Finset

noncomputable section

theorem greedyConfigurationLossSelectors_trajectory_error
    {V : Type*} [Fintype V] [DecidableEq V]
    {F J : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    {root : TripleOn V} {c d K : ℕ} {C : TripleSystemOn V}
    (H epsilon : ℝ)
    (hS : GreedyInvariant F S) (hroot : root ∈ S.available)
    (hC : C ∈ greedyConfigurationClass J S root c) (hcard : C.card = d + 1)
    (hrootInter : ∀ U ∈ (C ∩ S.available).erase root,
      (greedyClosedThreats F S U ∩ greedyClosedThreats F S root).card ≤ K)
    (hinter : ∀ U ∈ (C ∩ S.available).erase root,
      ∀ W ∈ (C ∩ S.available).erase root, U ≠ W →
        (greedyClosedThreats F S U ∩ greedyClosedThreats F S W).card ≤ K)
    (htrajectory : ∀ U ∈ (C ∩ S.available).erase root,
      |((greedyClosedThreats F S U).card : ℝ) - H| ≤ epsilon) :
    |((greedyConfigurationLossSelectors F S root C).card : ℝ) - (d - c : ℕ) * H| ≤
      (d - c : ℕ) * epsilon + (((d - c) + (d - c).choose 2) * K : ℕ) := by
  have hbound := abs_card_restricted_biUnion_sub ((C ∩ S.available).erase root)
    (greedyClosedThreats F S) (greedyClosedThreats F S root) K H epsilon
      hrootInter hinter htrajectory
  rw [greedyConfigurationClass_available_nonroot_card hS hroot hC hcard] at hbound
  exact hbound

end

end Erdos207
