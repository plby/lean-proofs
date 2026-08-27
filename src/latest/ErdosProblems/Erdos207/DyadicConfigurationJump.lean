/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CrudeConfigurationJumps
import ErdosProblems.Erdos207.DyadicCrudeCutoffs
import ErdosProblems.Erdos207.PowerAmbientBudgets

/-! # Uniform ambient powers for the actual crude configuration jump cutoffs -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem ambient_succ_pow_mul_power_le
    (N t : ℝ) (q r k : ℕ) (hN : 1 ≤ N) (ht : 0 ≤ t)
    (hconst : (2 : ℝ) ^ q ≤ t) (hr : r ≤ q) :
    (N + 1) ^ r * t ^ k ≤ N ^ r * t ^ (k + 1) := by
  calc
    _ ≤ (t * N ^ r) * t ^ k :=
      mul_le_mul_of_nonneg_right (ambient_succ_power_le_scale N t q r hN hconst hr) (pow_nonneg ht k)
    _ = _ := by rw [pow_succ]; ring

theorem dyadicConfigurationLossCutoff_le_power
    {V : Type*} [Fintype V] (q t k j c : ℕ) (H : ℝ≥0)
    (hN : 1 ≤ Fintype.card V) (ht : 4 ≤ t) (hconst : 2 ^ q ≤ t)
    (hj : j ≤ q) (hc : c + 4 ≤ j) (hH : (H : ℝ) ≤ (t : ℝ) * Fintype.card V) :
    (crudeConfigurationLossCutoff (dyadicCrudeThresholds V t k) H j c : ℝ) ≤
      (Fintype.card V : ℝ) ^ (j - c - 4) * (t : ℝ) ^ (k + 2) := by
  have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have hNR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  by_cases hterminal : c + 4 = j
  · rw [crudeConfigurationLossCutoff, if_pos hterminal]
    have hz : j - c - 4 = 0 := by omega
    rw [hz, pow_zero, one_mul]
    change 3 * (t : ℝ) ^ k + (t : ℝ) ^ k ≤ (t : ℝ) ^ (k + 2)
    have hp2 : (4 : ℝ) ≤ (t : ℝ) ^ 2 := by nlinarith
    calc
      _ = 4 * (t : ℝ) ^ k := by ring
      _ ≤ (t : ℝ) ^ 2 * (t : ℝ) ^ k := mul_le_mul_of_nonneg_right hp2 (by positivity)
      _ = _ := by rw [pow_add]; ring
  · rw [crudeConfigurationLossCutoff, if_neg hterminal]
    change (H : ℝ) * ((Fintype.card V + 1 : ℝ) ^ (j - c - 5) * (t : ℝ) ^ k) ≤ _
    have hroot := ambient_succ_pow_mul_power_le (Fintype.card V) t q (j - c - 5) k hNR
      htpos.le (by exact_mod_cast hconst) (by omega)
    have hz : j - c - 4 = (j - c - 5) + 1 := by omega
    calc
      _ ≤ ((t : ℝ) * Fintype.card V) *
          ((Fintype.card V : ℝ) ^ (j - c - 5) * (t : ℝ) ^ (k + 1)) := by gcongr
      _ = _ := by rw [hz, pow_succ, show k + 2 = (k + 1) + 1 by omega, pow_succ]; ring

theorem dyadicConfigurationSuccCutoff_le_power
    {V : Type*} [Fintype V] (q t k j c : ℕ) (H : ℝ≥0)
    (hN : 1 ≤ Fintype.card V) (ht : 4 ≤ t) (hconst : 2 ^ q ≤ t)
    (hj : j ≤ q) (hc : c + 5 ≤ j) (hH : (H : ℝ) ≤ (t : ℝ) * Fintype.card V) :
    max ((dyadicCrudeThresholds V t k).rooted j c : ℝ)
      (crudeConfigurationLossCutoff (dyadicCrudeThresholds V t k) H j (c + 1) : ℝ) ≤
        (Fintype.card V : ℝ) ^ (j - c - 5) * (t : ℝ) ^ (k + 2) := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  apply max_le
  · have hb := ambient_succ_pow_mul_power_le (Fintype.card V) t q (j - c - 5) k
      (by exact_mod_cast hN) (by positivity) (by exact_mod_cast hconst) (by omega)
    apply hb.trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ htR (by omega)) (by positivity)
  · have hb := dyadicConfigurationLossCutoff_le_power q t k j (c + 1) H hN ht hconst hj (by omega) hH
    have hz : j - (c + 1) - 4 = j - c - 5 := by omega
    simpa only [hz] using hb

theorem CrudeStateBounds.dyadic_configuration_succ_jump
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q t k : ℕ}
    (h : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (j c : ℕ) (hj : j ≤ q) (hc : c + 5 ≤ j) (H : ℝ≥0)
    (hN : 1 ≤ Fintype.card V) (ht : 4 ≤ t) (hconst : 2 ^ q ≤ t)
    (hH : (H : ℝ) ≤ (t : ℝ) * Fintype.card V)
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    {root T : TripleOn V} (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hthreat : ((greedyClosedThreats F S T).card : ℝ≥0) ≤ H) :
    |((greedyConfigurationClass (forbiddenFamilyOfOrder F j) (greedyStep F S T) root (c + 1)).card : ℝ) -
      (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root (c + 1)).card| ≤
        (Fintype.card V : ℝ) ^ (j - c - 5) * (t : ℝ) ^ (k + 2) :=
  (h.configuration_succ_jump j c hj hc H hS hpack hroot hT hthreat).trans
    (dyadicConfigurationSuccCutoff_le_power q t k j c H hN ht hconst hj hc hH)

theorem CrudeStateBounds.dyadic_configuration_zero_jump
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {q t k : ℕ}
    (h : CrudeStateBounds F S q (dyadicCrudeThresholds V t k))
    (j : ℕ) (hj : j ≤ q) (hc : 4 ≤ j) (H : ℝ≥0)
    (hN : 1 ≤ Fintype.card V) (ht : 4 ≤ t) (hconst : 2 ^ q ≤ t)
    (hH : (H : ℝ) ≤ (t : ℝ) * Fintype.card V)
    (hS : GreedyInvariant F S) (hpack : ∀ D ∈ F, IsPackingOn D)
    {root T : TripleOn V} (hroot : root ∈ S.available)
    (hT : T ∈ S.available \ greedyClosedThreats F S root)
    (hthreat : ((greedyClosedThreats F S T).card : ℝ≥0) ≤ H) :
    |((greedyConfigurationClass (forbiddenFamilyOfOrder F j) (greedyStep F S T) root 0).card : ℝ) -
      (greedyConfigurationClass (forbiddenFamilyOfOrder F j) S root 0).card| ≤
        (Fintype.card V : ℝ) ^ (j - 4) * (t : ℝ) ^ (k + 2) := by
  exact (h.configuration_zero_jump j hj hc H hS hpack hroot hT hthreat).trans
    (dyadicConfigurationLossCutoff_le_power q t k j 0 H hN ht hconst hj hc hH)

end

end Erdos207
