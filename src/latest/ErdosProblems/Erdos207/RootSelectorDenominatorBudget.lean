/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GlobalPairTrajectory
import ErdosProblems.Erdos207.CoupledDenominatorBudget

/-! # Root-preserving selector denominators from trajectory estimates -/

namespace Erdos207

open Finset

noncomputable section

theorem root_selector_denominator_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (root : TripleOn V)
    (L x e H C k : ℝ) (hL : 0 < L) (hx : 0 < x)
    (hC : 0 ≤ C) (hk : 0 ≤ k) (he : e ≤ x / 4) (hlarge : 12 * (C + k) ≤ L)
    (havailable : |(S.available.card : ℝ) - L * x / 3| ≤ L * e / 3)
    (hthreat : |((greedyClosedThreats F S root).card : ℝ) - H| ≤ k * e)
    (hH : |H| ≤ C * x) (hxe : x ≤ L * e) :
    let R := S.available \ greedyClosedThreats F S root
    L * x / 6 ≤ (R.card : ℝ) ∧
      |(R.card : ℝ) - L * x / 3| ≤ (1 / 3 + C + k) * L * e := by
  dsimp only
  have hsub : greedyClosedThreats F S root ⊆ S.available := inter_subset_left
  have hD : ((greedyClosedThreats F S root).card : ℝ) ≤ (C + k) * x := by
    have ht := (abs_le.mp hthreat).2
    have hh := le_abs_self H
    have he' := mul_le_mul_of_nonneg_left (show e ≤ x by linarith) hk
    nlinarith only [ht, hh, hH, he']
  rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  constructor
  · exact coupled_selector_denominator_lower hL hx he havailable hD hlarge
  · convert coupled_selector_denominator_error (Nat.cast_nonneg _) (add_nonneg hC hk)
      havailable hD hxe using 1
    ring

end

end Erdos207
