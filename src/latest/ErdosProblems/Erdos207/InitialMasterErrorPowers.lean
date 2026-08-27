/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPatternGraphLaw
import Mathlib.Analysis.SpecificLimits.Normed

/-! # The actual initial graph-law error meets every fixed backward power budget -/

namespace Erdos207

open Filter
open scoped Topology NNReal

theorem eventually_polynomial_geometric_le_power
    (R k exponent : ℕ) (A B : ℝ≥0) (hB : 0 < B) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ n : ℕ, n ≤ t ^ R →
      A * (n + 1 : ℝ≥0) ^ k * (1 / 2 : ℝ≥0) ^ t ≤ B / (t : ℝ≥0) ^ exponent := by
  have hlim : Tendsto (fun t : ℕ ↦ ((A : ℝ) * 2 ^ k) *
      ((t : ℝ) ^ (R * k + exponent) * (1 / 2 : ℝ) ^ t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_const_mul_const_pow_of_lt_one (R * k + exponent)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
          ((A : ℝ) * 2 ^ k)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < B by exact_mod_cast hB)))
  refine ⟨max 1 T, le_max_left _ _, ?_⟩
  intro t ht n hn
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  have ht0 : (0 : ℝ) < t := zero_lt_one.trans_le htR
  have hnR : (n : ℝ) ≤ (t : ℝ) ^ R := by exact_mod_cast hn
  have hnplus : (n + 1 : ℝ) ≤ 2 * (t : ℝ) ^ R := by
    have hp := one_le_pow₀ htR (n := R)
    linarith only [hnR, hp]
  have hbound : (A : ℝ) * (n + 1 : ℝ) ^ k * (1 / 2 : ℝ) ^ t * (t : ℝ) ^ exponent ≤
      ((A : ℝ) * 2 ^ k) * ((t : ℝ) ^ (R * k + exponent) * (1 / 2 : ℝ) ^ t) := by
    calc
      _ ≤ (A : ℝ) * (2 * (t : ℝ) ^ R) ^ k * (1 / 2 : ℝ) ^ t * (t : ℝ) ^ exponent := by
        gcongr
      _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring
  have hfinal : (A : ℝ) * (n + 1 : ℝ) ^ k * (1 / 2 : ℝ) ^ t ≤ (B : ℝ) / (t : ℝ) ^ exponent :=
    (le_div_iff₀ (pow_pos ht0 _)).mpr (hbound.trans (hT t ((le_max_right _ _).trans ht)).le)
  exact_mod_cast hfinal

theorem eventually_initialPatternGraphError_le_power
    (q h ell R exponent : ℕ) (B : ℝ≥0) (hB : 0 < B) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t → ∀ n : ℕ, n ≤ t ^ R →
      initialPatternGraphError q h ell n t ≤ B / (t : ℝ≥0) ^ exponent := by
  exact eventually_polynomial_geometric_le_power R (6 + 2 * h ^ 2) exponent
    (8 * (q + 1 : ℝ≥0) ^ 2 + 5 * (ell + 1 : ℝ≥0) + 2 * (ell + 1 : ℝ≥0) * h ^ 2) B hB

end Erdos207
