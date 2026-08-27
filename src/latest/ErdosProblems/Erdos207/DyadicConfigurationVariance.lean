/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DyadicConfigurationJump
import ErdosProblems.Erdos207.CrudeConfigurationVariance
import ErdosProblems.Erdos207.ConfigurationVariancePower

/-! # The actual configuration second moments on the common power scale -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem CrudeStateBounds.dyadic_configuration_succ_variance
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q t k b : ℕ}
    (h : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (j c : ℕ) (hj : j ≤ q) (hc : c + 5 ≤ j) (H : ℝ≥0)
    (hN : 1 ≤ Fintype.card V) (ht : 6 ≤ t) (hconst : 2 ^ q ≤ t) (hqt : q ≤ t)
    (hH : (H : ℝ) ≤ (t : ℝ) * Fintype.card V)
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    {root : TripleOn V} (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hthreat : ∀ T ∈ S.available, ((greedyClosedThreats F S T).card : ℝ≥0) ≤ H)
    (hprev : ((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root c).card : ℝ) ≤
      (t : ℝ) * (Fintype.card V : ℝ) ^ (j - c - 3))
    (hcurr : ((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root (c + 1)).card : ℝ) ≤
      (t : ℝ) * (Fintype.card V : ℝ) ^ (j - c - 4))
    (hden : (Fintype.card V : ℝ) ^ 3 / (6 * (t : ℝ) ^ (5 * b + 1)) ≤
      (S.available \ greedyClosedThreats F S root).card) :
    (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
      (fun S' ↦ (((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S' root (c + 1)).card : ℝ) -
        (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root (c + 1)).card) ^ 2) ≤
      (Fintype.card V : ℝ) ^ (2 * (j - c - 5)) / Fintype.card V * (t : ℝ) ^ (k + 5 * b + 8) := by
  let N : ℝ := Fintype.card V
  let z := j - c - 5
  let vprev : ℝ := (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root c).card
  let vcurr : ℝ := (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root (c + 1)).card
  let M : ℝ := max ((dyadicCrudeThresholds V t k).rooted j c : ℝ)
    (crudeConfigurationLossCutoff (dyadicCrudeThresholds V t k) H j (c + 1) : ℝ)
  have hNpos : 0 < N := by dsimp only [N]; exact_mod_cast (show 0 < Fintype.card V by omega)
  have htR : (6 : ℝ) ≤ t := by exact_mod_cast ht
  have hm := dyadicConfigurationSuccCutoff_le_power q t k j c H hN (by omega) hconst hj hc hH
  have hraw := h.configuration_succ_variance j c hj hc H hS hpack hroot hR hthreat
  have hprevExp : j - c - 3 = z + 2 := by dsimp only [z]; omega
  have hcurrExp : j - c - 4 = z + 1 := by dsimp only [z]; omega
  have hnum := configuration_move_numerator_power N t vprev vcurr (j - 3 - c : ℕ)
    (j - 3 - (c + 1) : ℕ) H z hNpos.le (by linarith) (by positivity) (by positivity)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity)
    (by simpa only [hprevExp] using hprev) (by simpa only [hcurrExp] using hcurr)
    (by exact_mod_cast (show j - 3 - c ≤ t by omega))
    (by exact_mod_cast (show j - 3 - (c + 1) ≤ t by omega)) hH
  exact configuration_second_moment_power N t M
    (vprev * (j - 3 - c : ℕ) + vcurr * ((j - 3 - (c + 1) : ℕ) * (H : ℝ)))
    (S.available \ greedyClosedThreats F S root).card _ z k b hNpos htR
    (by dsimp only [M]; positivity) (by dsimp only [vprev, vcurr]; positivity) hm hnum hden hraw

theorem CrudeStateBounds.dyadic_configuration_zero_variance
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q t k b : ℕ}
    (h : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (j : ℕ) (hj : j ≤ q) (hc : 4 ≤ j) (H : ℝ≥0)
    (hN : 1 ≤ Fintype.card V) (ht : 6 ≤ t) (hconst : 2 ^ q ≤ t) (hqt : q ≤ t)
    (hH : (H : ℝ) ≤ (t : ℝ) * Fintype.card V)
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    {root : TripleOn V} (hroot : root ∈ S.available)
    (hR : (S.available \ greedyClosedThreats F S root).Nonempty)
    (hthreat : ∀ T ∈ S.available, ((greedyClosedThreats F S T).card : ℝ≥0) ≤ H)
    (hcurr : ((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root 0).card : ℝ) ≤
      (t : ℝ) * (Fintype.card V : ℝ) ^ (j - 3))
    (hden : (Fintype.card V : ℝ) ^ 3 / (6 * (t : ℝ) ^ (5 * b + 1)) ≤
      (S.available \ greedyClosedThreats F S root).card) :
    (restrictedGreedyKernel F S (S.available \ greedyClosedThreats F S root) hR).expectationReal
      (fun S' ↦ (((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S' root 0).card : ℝ) -
        (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root 0).card) ^ 2) ≤
      (Fintype.card V : ℝ) ^ (2 * (j - 4)) / Fintype.card V * (t : ℝ) ^ (k + 5 * b + 8) := by
  let N : ℝ := Fintype.card V
  let z := j - 4
  let vcurr : ℝ := (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root 0).card
  let M : ℝ := crudeConfigurationLossCutoff (dyadicCrudeThresholds V t k) H j 0
  have hNpos : 0 < N := by dsimp only [N]; exact_mod_cast (show 0 < Fintype.card V by omega)
  have htR : (6 : ℝ) ≤ t := by exact_mod_cast ht
  have hm := dyadicConfigurationLossCutoff_le_power q t k j 0 H hN (by omega) hconst hj hc hH
  have hraw := h.configuration_zero_variance j hj hc H hS hpack hroot hR hthreat
  have hcurrExp : j - 3 = z + 1 := by dsimp only [z]; omega
  have hnum' := configuration_move_numerator_power N t 0 vcurr 0 (j - 3 : ℕ) H z
    hNpos.le (by linarith) le_rfl (by positivity) le_rfl (Nat.cast_nonneg _) (by positivity)
    (by positivity) (by simpa only [hcurrExp] using hcurr) (by positivity)
    (by exact_mod_cast (show j - 3 ≤ t by omega)) hH
  have hnum : vcurr * ((j - 3 : ℕ) * (H : ℝ)) ≤ (t : ℝ) ^ 4 * N ^ (z + 2) := by
    simpa only [zero_mul, zero_add] using hnum'
  exact configuration_second_moment_power N t M (vcurr * ((j - 3 : ℕ) * (H : ℝ)))
    (S.available \ greedyClosedThreats F S root).card _ z k b hNpos htR
    (by dsimp only [M]; positivity) (by dsimp only [vcurr]; positivity) hm hnum hden hraw

end

end Erdos207
