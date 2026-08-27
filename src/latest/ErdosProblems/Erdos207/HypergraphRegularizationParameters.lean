/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.HypergraphRegularizationTransition
import ErdosProblems.Erdos207.RegularizationBinomialBudget

/-! # Instantiating the weighted sampler from actual degree and order bounds -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem finiteHypergraphMaxDegree_mono
    {V : Type*} [Fintype V] [DecidableEq V] {G H : Finset (Finset V)} (hGH : G ⊆ H) :
    finiteHypergraphMaxDegree G ≤ finiteHypergraphMaxDegree H := by
  apply (finiteHypergraphMaxDegree_le_iff _ _).mpr
  intro v
  exact (finiteHypergraphDegree_mono hGH v).trans (finiteHypergraphDegree_le_max H v)

theorem uniformIncident_inter_card_le_degree
    {V : Type*} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (k : ℕ) (v : V) :
    (uniformIncidentSets k v ∩ H).card ≤ finiteHypergraphDegree H v := by
  apply card_le_card
  intro E hE
  have hm := mem_inter.mp hE
  exact mem_filter.mpr ⟨hm.2, (mem_uniformIncidentSets_iff.mp hm.1).2⟩

theorem regularization_order_bounds
    (n k : ℕ) (hk : 2 ≤ k) (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ n) :
    0 < n ∧ k - 1 ≤ n := by
  have hr : 0 < k - 1 := by omega
  have hfactor : 0 < 16 * 2 ^ (k - 1) := by positivity
  constructor
  · exact (Nat.mul_pos hfactor hr).trans_le hsize
  · exact (Nat.le_mul_of_pos_left (k - 1) hfactor).trans hsize

theorem uniformBlocked_budget_of_max_degree
    {V : Type*} [Fintype V] [DecidableEq V] (H : Finset (Finset V)) {k : ℕ}
    (hk : 1 ≤ k) (v : V)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H ≤
      (1 / 4 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)) :
    (2 : ℝ≥0) ^ (k - 1) * (uniformIncidentSets k v ∩ H).card ≤
      (1 / 8 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1) := by
  have hcard : ((uniformIncidentSets k v ∩ H).card : ℝ≥0) ≤ finiteHypergraphMaxDegree H := by
    exact_mod_cast (uniformIncident_inter_card_le_degree H k v).trans (finiteHypergraphDegree_le_max H v)
  apply (mul_le_mul_of_nonneg_left hcard (show (0 : ℝ≥0) ≤ 2 ^ (k - 1) from zero_le)).trans
  have hpow : (2 : ℝ≥0) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  apply (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ≥0) < 2)).mp
  calc
    _ = (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H := by rw [hpow]; ring
    _ ≤ _ := hdensity
    _ = _ := by ring

def hypergraphRegularizationParameters
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G H : Finset (Finset V)) (hGH : G ⊆ H) {k : ℕ} (hk : 2 ≤ k)
    (hgap : 0 < finiteHypergraphDegreeGap G)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H ≤
      (1 / 4 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)) :
    WeightedUniformSamplerParameters (finiteHypergraphRegularizationWeight G)
      (finiteHypergraphDegreeGap G) k := by
  refine ⟨hk, by exact_mod_cast hgap,
    (fun v ↦ (finiteHypergraphRegularizationWeight_bounds G v).1),
    (fun v ↦ (finiteHypergraphRegularizationWeight_bounds G v).2),
    (regularization_order_bounds _ _ hk hsize).2, ?_⟩
  have hg : (finiteHypergraphDegreeGap G : ℝ≥0) ≤ finiteHypergraphMaxDegree H := by
    exact_mod_cast (Nat.sub_le (finiteHypergraphMaxDegree G) (finiteHypergraphMinDegree G)).trans
      (finiteHypergraphMaxDegree_mono hGH)
  calc
    _ ≤ (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H := mul_le_mul_of_nonneg_left hg zero_le
    _ ≤ _ := hdensity
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        ((div_le_one₀ (by norm_num : (0 : ℝ≥0) < 4)).mpr (by norm_num))
        (show (0 : ℝ≥0) ≤ Nat.choose (Fintype.card V) (k - 1) from zero_le)

theorem hypergraphRegularizationParameters_failure_probability
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G H : Finset (Finset V)) (hGH : G ⊆ H) {k : ℕ} (hk : 2 ≤ k)
    (hgap : 0 < finiteHypergraphDegreeGap G)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (hdensity : (2 : ℝ≥0) ^ k * finiteHypergraphMaxDegree H ≤
      (1 / 4 : ℝ≥0) * Nat.choose (Fintype.card V) (k - 1)) :
    ((hypergraphRegularizationParameters G H hGH hk hgap hsize hdensity).law.probability
      (fun ω ↦ ¬ WeightedRegularizationStepGood (fun v ↦ finiteHypergraphDegree G v)
        (finiteHypergraphDegreeGap G) H ω) : ℝ) ≤
      2 * Fintype.card V * Real.exp (-(finiteHypergraphDegreeGap G : ℝ) / 8192) := by
  apply (hypergraphRegularizationParameters G H hGH hk hgap hsize hdensity).step_failure_probability
    H (fun v ↦ finiteHypergraphDegree G v) (finiteHypergraphMaxDegree G)
    (finiteHypergraphRegularizationWeight_center G)
  · have hn := (regularization_order_bounds _ _ hk hsize).1
    simpa only [Nat.sub_sub] using
      regularization_binomial_budget (Fintype.card V) (k - 1) hn (by omega) hsize
  · intro v
    exact uniformBlocked_budget_of_max_degree H (by omega) v hdensity

end

end Erdos207
