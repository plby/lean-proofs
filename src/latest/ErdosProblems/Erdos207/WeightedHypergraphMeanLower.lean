/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightedHypergraphIncidence

/-! # Separating the normalization loss and forbidden-edge loss in degree means -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem uniformNormalizer_incident_fraction_le
    {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (w : V → ℝ≥0) (a epsilon : ℝ≥0) (hr : 1 ≤ r) (v : V)
    (hlo : ∀ u, a ≤ w u) (hhi : ∀ u, w u ≤ 2 * a)
    (hbudget : (2 : ℝ≥0) ^ r * Nat.choose (Fintype.card V - 1) (r - 1) ≤
      epsilon * Nat.choose (Fintype.card V) r) :
    ∑ S ∈ uniformIncidentSets r v, ∏ u ∈ S, w u ≤ epsilon * uniformWeightNormalizer w r := by
  calc
    _ ≤ (Nat.choose (Fintype.card V - 1) (r - 1) : ℝ≥0) * (2 * a) ^ r :=
      uniformIncident_weight_sum_le w (2 * a) hr v hhi
    _ = ((2 : ℝ≥0) ^ r * Nat.choose (Fintype.card V - 1) (r - 1)) * a ^ r := by
      rw [mul_pow]; ring
    _ ≤ (epsilon * Nat.choose (Fintype.card V) r) * a ^ r :=
      mul_le_mul_of_nonneg_right hbudget zero_le
    _ ≤ epsilon * uniformWeightNormalizer w r := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (uniformWeightNormalizer_lower w a r hlo) zero_le

theorem uniformIncident_probability_lower
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → ℝ≥0) (a epsilon : ℝ≥0) (hk : 2 ≤ k) (v : V)
    (hlo : ∀ u, a ≤ w u) (hhi : ∀ u, w u ≤ 2 * a)
    (hnorm : 0 < uniformWeightNormalizer w (k - 1))
    (hbudget : (2 : ℝ≥0) ^ (k - 1) * Nat.choose (Fintype.card V - 1) (k - 2) ≤
      epsilon * Nat.choose (Fintype.card V) (k - 1)) :
    w v ≤ (∑ E ∈ uniformIncidentSets k v, uniformEdgeProbability w k E) + epsilon * w v := by
  have hfrac : (∑ S ∈ uniformIncidentSets (k - 1) v, ∏ u ∈ S, w u) ≤
      epsilon * uniformWeightNormalizer w (k - 1) := by
    apply uniformNormalizer_incident_fraction_le w a epsilon (by omega) v hlo hhi
    simpa only [Nat.sub_sub] using hbudget
  have havoid : uniformWeightNormalizer w (k - 1) ≤
      (∑ S ∈ ((univ : Finset V).erase v).powersetCard (k - 1), ∏ u ∈ S, w u) +
        epsilon * uniformWeightNormalizer w (k - 1) := by
    conv_lhs => rw [uniformWeightNormalizer_split w (k - 1) v]
    exact add_le_add le_rfl hfrac
  rw [uniformIncident_probability_sum_eq w (by omega) v]
  apply (mul_le_mul_iff_left₀ hnorm).mp
  calc
    _ ≤ w v * ((∑ S ∈ ((univ : Finset V).erase v).powersetCard (k - 1), ∏ u ∈ S, w u) +
        epsilon * uniformWeightNormalizer w (k - 1)) :=
      mul_le_mul_of_nonneg_left havoid zero_le
    _ = _ := by
      rw [add_mul, div_mul_cancel₀ _ hnorm.ne']
      ring

theorem uniformBlocked_probability_sum_le
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → ℝ≥0) (a eta : ℝ≥0) (H : Finset (Finset V)) (v : V)
    (ha : 0 < a) (hlo : ∀ u, a ≤ w u) (hhi : ∀ u, w u ≤ 2 * a)
    (hr : k - 1 ≤ Fintype.card V)
    (hbudget : (2 : ℝ≥0) ^ (k - 1) * (uniformIncidentSets k v ∩ H).card ≤
      eta * Nat.choose (Fintype.card V) (k - 1)) :
    ∑ E ∈ uniformIncidentSets k v ∩ H, uniformEdgeProbability w k E ≤ eta * w v := by
  have hC : (0 : ℝ≥0) < Nat.choose (Fintype.card V) (k - 1) := by
    exact_mod_cast Nat.choose_pos hr
  calc
    _ ≤ ∑ _E ∈ uniformIncidentSets k v ∩ H,
        w v * 2 ^ (k - 1) / (Nat.choose (Fintype.card V) (k - 1) : ℝ≥0) := by
      apply sum_le_sum
      intro E hE
      have hm := mem_uniformIncidentSets_iff.mp (mem_inter.mp hE).1
      exact uniformEdgeProbability_root_le w a ha hlo hhi hm.1 hm.2
    _ = w v * ((2 : ℝ≥0) ^ (k - 1) * (uniformIncidentSets k v ∩ H).card) /
        (Nat.choose (Fintype.card V) (k - 1) : ℝ≥0) := by simp; ring
    _ ≤ w v * (eta * Nat.choose (Fintype.card V) (k - 1)) /
        (Nat.choose (Fintype.card V) (k - 1) : ℝ≥0) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget zero_le) zero_le
    _ = _ := by field_simp

theorem uniformFresh_probability_sum_bounds
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → ℝ≥0) (a epsilon eta : ℝ≥0) (H : Finset (Finset V))
    (hk : 2 ≤ k) (v : V) (ha : 0 < a)
    (hlo : ∀ u, a ≤ w u) (hhi : ∀ u, w u ≤ 2 * a)
    (hr : k - 1 ≤ Fintype.card V)
    (hnormal : (2 : ℝ≥0) ^ (k - 1) * Nat.choose (Fintype.card V - 1) (k - 2) ≤
      epsilon * Nat.choose (Fintype.card V) (k - 1))
    (hblocked : (2 : ℝ≥0) ^ (k - 1) * (uniformIncidentSets k v ∩ H).card ≤
      eta * Nat.choose (Fintype.card V) (k - 1)) :
    (∑ E ∈ uniformIncidentSets k v \ H, uniformEdgeProbability w k E) ≤ w v ∧
      w v ≤ (∑ E ∈ uniformIncidentSets k v \ H, uniformEdgeProbability w k E) +
        (epsilon + eta) * w v := by
  have hnorm := uniformWeightNormalizer_pos w a (k - 1) ha hlo hr
  have hupper := uniformIncident_probability_sum_le w (by omega) v hnorm
  have hlower := uniformIncident_probability_lower w a epsilon hk v hlo hhi hnorm hnormal
  have hblock := uniformBlocked_probability_sum_le w a eta H v ha hlo hhi hr hblocked
  have hfresh : ((uniformIncidentSets k v).filter fun E ↦ E ∉ H) =
      uniformIncidentSets k v \ H := by ext E; simp
  have hused : ((uniformIncidentSets k v).filter fun E ↦ E ∈ H) =
      uniformIncidentSets k v ∩ H := by ext E; simp
  have hsplit := sum_filter_not_add_sum_filter (uniformIncidentSets k v)
    (fun E ↦ E ∈ H) (uniformEdgeProbability w k)
  rw [hfresh, hused] at hsplit
  constructor
  · exact (sum_le_sum_of_subset sdiff_subset).trans hupper
  · apply hlower.trans
    rw [← hsplit]
    calc
      _ ≤ ((∑ E ∈ uniformIncidentSets k v \ H, uniformEdgeProbability w k E) +
          eta * w v) + epsilon * w v := add_le_add (add_le_add le_rfl hblock) le_rfl
      _ = _ := by ring

end

end Erdos207
