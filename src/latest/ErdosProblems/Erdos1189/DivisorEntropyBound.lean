/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The sharp uniform divisor-entropy bound for finite prime-coordinate profiles.
Informal source: BBMST Lemma 6.3.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.DivisorEntropyNormalization

namespace Erdos1189

open Finset Filter

lemma coordinateMass_le_weight (S : Finset (ℕ × ℕ)) (hS : ∀ c ∈ S, c.1.Prime) :
    coordinateMass S ≤ coordinateWeight S := by
  apply sum_le_sum
  intro c hc
  have hp : (2 : ℝ) ≤ c.1 := by exact_mod_cast (hS c hc).two_le
  have hw := logIncrement_le_one c.2
  linarith

lemma coordinateMass_le_divisorEntropyBound (S : Finset (ℕ × ℕ))
    (hS : ∀ c ∈ S, c.1.Prime) {k : ℕ} (hk : 0 < precedingFrameIndex k)
    (hweight : coordinateWeight S ≤ k) : coordinateMass S ≤ divisorEntropyBound k := by
  have hx : (0 : ℝ) < precedingFrameIndex k := by exact_mod_cast hk
  have h := coordinate_knapsack S hS hx
  rw [counting_coordinate_weight] at h
  apply h.trans
  unfold divisorEntropyBound
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_right (by linarith) hx.le

theorem coordinateMass_eventually_upper {b : ℝ} (hb : 2 * Real.sqrt tau < b) :
    ∀ᶠ k : ℕ in atTop, ∀ S : Finset (ℕ × ℕ), (∀ c ∈ S, c.1.Prime) →
      coordinateWeight S ≤ k →
      coordinateMass S * Real.sqrt (Real.log k) / Real.sqrt k < b := by
  filter_upwards [(tendsto_order.mp divisorEntropyBound_asymptotic).2 b hb,
    precedingFrameIndex_tendsto.eventually (eventually_gt_atTop 0)] with k hk hj S hS hweight
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (coordinateMass_le_divisorEntropyBound S hS hj hweight) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)).trans_lt hk

theorem exists_uniform_coordinateMass_bound {b : ℝ} (hb : 2 * Real.sqrt tau < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, ∀ S : Finset (ℕ × ℕ),
      (∀ c ∈ S, c.1.Prime) → coordinateWeight S ≤ k →
      coordinateMass S ≤ b * Real.sqrt ((k : ℝ) / Real.log k) + C := by
  have hb0 : 0 < b := lt_trans (mul_pos (by norm_num) (Real.sqrt_pos.mpr tau_pos)) hb
  obtain ⟨K, hK⟩ := eventually_atTop.mp (coordinateMass_eventually_upper hb)
  refine ⟨((max K 2 : ℕ) : ℝ), by positivity, ?_⟩
  intro k S hS hweight
  by_cases hk : max K 2 ≤ k
  · have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    have hsqk := Real.sqrt_pos.mpr (zero_lt_one.trans hk1)
    have hsql := Real.sqrt_pos.mpr (Real.log_pos hk1)
    have hn := hK k (le_trans (le_max_left _ _) hk) S hS hweight
    have hmul := (div_lt_iff₀ hsqk).mp hn
    have hmass : coordinateMass S < b * Real.sqrt ((k : ℝ) / Real.log k) := by
      rw [Real.sqrt_div (Nat.cast_nonneg k), ← mul_div_assoc]
      exact (lt_div_iff₀ hsql).mpr hmul
    have hC : (0 : ℝ) ≤ max K 2 := by positivity
    linarith
  · have hmass := (coordinateMass_le_weight S hS).trans hweight
    have hsmall : (k : ℝ) ≤ max K 2 := by exact_mod_cast (le_of_not_ge hk)
    have hpos := mul_nonneg hb0.le (Real.sqrt_nonneg ((k : ℝ) / Real.log k))
    linarith

end Erdos1189
