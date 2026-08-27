/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightedUniformHypergraph

/-! # Exact incident-edge weighted sums and their mean upper bound -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def uniformIncidentSets
    {V : Type*} [Fintype V] [DecidableEq V] (k : ℕ) (v : V) : Finset (Finset V) :=
  ((univ : Finset V).powersetCard k).filter fun E ↦ v ∈ E

theorem mem_uniformIncidentSets_iff
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} {v : V} {E : Finset V} :
    E ∈ uniformIncidentSets k v ↔ E.card = k ∧ v ∈ E := by
  simp [uniformIncidentSets]

theorem sum_uniformIncidentSets_erase
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (hk : 1 ≤ k) (v : V) (f : Finset V → ℝ≥0) :
    ∑ E ∈ uniformIncidentSets k v, f (E.erase v) =
      ∑ S ∈ ((univ : Finset V).erase v).powersetCard (k - 1), f S := by
  apply sum_bij (fun E _ ↦ E.erase v)
  · intro E hE
    have hm := mem_uniformIncidentSets_iff.mp hE
    apply mem_powersetCard.mpr
    refine ⟨?_, ?_⟩
    · intro u hu
      exact mem_erase.mpr ⟨(mem_erase.mp hu).1, mem_univ _⟩
    · rw [card_erase_of_mem hm.2, hm.1]
  · intro E hE D hD heq
    have hEv := (mem_uniformIncidentSets_iff.mp hE).2
    have hDv := (mem_uniformIncidentSets_iff.mp hD).2
    have h := congrArg (insert v) heq
    simpa only [insert_erase hEv, insert_erase hDv] using h
  · intro S hS
    have hm := mem_powersetCard.mp hS
    have hv : v ∉ S := fun h ↦ (mem_erase.mp (hm.1 h)).1 rfl
    refine ⟨insert v S, mem_uniformIncidentSets_iff.mpr ⟨?_, mem_insert_self _ _⟩, ?_⟩
    · rw [card_insert_of_notMem hv, hm.2]
      omega
    · simp [hv]
  · intro E hE
    rfl

theorem card_uniformIncidentSets
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ} (hk : 1 ≤ k) (v : V) :
    (uniformIncidentSets k v).card = Nat.choose (Fintype.card V - 1) (k - 1) := by
  have h := sum_uniformIncidentSets_erase hk v (fun _ ↦ 1)
  simpa only [sum_const, nsmul_eq_mul, mul_one, card_powersetCard,
    card_erase_of_mem (mem_univ v), card_univ, Nat.cast_inj] using h

theorem uniformIncident_weight_sum
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → ℝ≥0) (hk : 1 ≤ k) (v : V) :
    ∑ E ∈ uniformIncidentSets k v, ∏ u ∈ E, w u =
      w v * ∑ S ∈ ((univ : Finset V).erase v).powersetCard (k - 1), ∏ u ∈ S, w u := by
  calc
    _ = ∑ E ∈ uniformIncidentSets k v, w v * ∏ u ∈ E.erase v, w u := by
      apply sum_congr rfl
      intro E hE
      exact (mul_prod_erase E w (mem_uniformIncidentSets_iff.mp hE).2).symm
    _ = _ := by
      rw [sum_uniformIncidentSets_erase hk v (fun S ↦ w v * ∏ u ∈ S, w u), mul_sum]

theorem uniformIncident_probability_sum_le
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → ℝ≥0) (hk : 1 ≤ k) (v : V)
    (hnorm : 0 < uniformWeightNormalizer w (k - 1)) :
    ∑ E ∈ uniformIncidentSets k v, uniformEdgeProbability w k E ≤ w v := by
  unfold uniformEdgeProbability
  simp only [div_eq_mul_inv]
  rw [← sum_mul, uniformIncident_weight_sum w hk v, ← div_eq_mul_inv]
  apply (div_le_iff₀ hnorm).mpr
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply sum_le_sum_of_subset
  intro S hS
  have hm := mem_powersetCard.mp hS
  exact mem_powersetCard.mpr ⟨subset_univ _, hm.2⟩

theorem uniformIncident_probability_sum_eq
    {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
    (w : V → ℝ≥0) (hk : 1 ≤ k) (v : V) :
    ∑ E ∈ uniformIncidentSets k v, uniformEdgeProbability w k E =
      (w v * ∑ S ∈ ((univ : Finset V).erase v).powersetCard (k - 1), ∏ u ∈ S, w u) /
        uniformWeightNormalizer w (k - 1) := by
  unfold uniformEdgeProbability
  simp only [div_eq_mul_inv]
  rw [← sum_mul, uniformIncident_weight_sum w hk v]

theorem uniformWeightNormalizer_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (w : V → ℝ≥0) (r : ℕ) (v : V) :
    uniformWeightNormalizer w r =
      (∑ S ∈ ((univ : Finset V).erase v).powersetCard r, ∏ u ∈ S, w u) +
        ∑ S ∈ uniformIncidentSets r v, ∏ u ∈ S, w u := by
  have havoid : (((univ : Finset V).powersetCard r).filter fun S ↦ v ∉ S) =
      ((univ : Finset V).erase v).powersetCard r := by
    ext S
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and]
    constructor
    · rintro ⟨hcard, hv⟩
      refine ⟨?_, hcard⟩
      intro u hu
      exact mem_erase.mpr ⟨fun heq ↦ hv (heq ▸ hu), mem_univ _⟩
    · rintro ⟨hS, hcard⟩
      exact ⟨hcard, fun hv ↦ (mem_erase.mp (hS hv)).1 rfl⟩
  have h := sum_filter_not_add_sum_filter ((univ : Finset V).powersetCard r)
    (fun S ↦ v ∈ S) (fun S ↦ ∏ u ∈ S, w u)
  rw [havoid] at h
  exact h.symm

theorem uniformIncident_weight_sum_le
    {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (w : V → ℝ≥0) (b : ℝ≥0) (hr : 1 ≤ r) (v : V) (hw : ∀ u, w u ≤ b) :
    ∑ S ∈ uniformIncidentSets r v, ∏ u ∈ S, w u ≤
      (Nat.choose (Fintype.card V - 1) (r - 1) : ℝ≥0) * b ^ r := by
  calc
    _ ≤ ∑ _S ∈ uniformIncidentSets r v, b ^ r := by
      apply sum_le_sum
      intro S hS
      simpa only [prod_const, (mem_uniformIncidentSets_iff.mp hS).1] using
        prod_le_prod' (fun u (_hu : u ∈ S) ↦ hw u)
    _ = _ := by simp [card_uniformIncidentSets hr v]

end

end Erdos207
