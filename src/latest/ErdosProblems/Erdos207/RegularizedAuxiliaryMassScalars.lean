/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveRegularizationPowerScalars

/-! # The regularizer's inner margin and auxiliary mass normalization -/

namespace Erdos207

open scoped NNReal

theorem reserve_inner_margin_for_graph_mass
    (u n p tau : ℝ≥0) (hp : p ≤ 1) (htau : tau ≤ 1)
    (hinner : u ≤ p ^ 4 * tau ^ 6 * n / 1536) : u ≤ p * n / 8 := by
  have hp4 : p ^ 4 ≤ p := by
    simpa only [pow_one] using pow_le_pow_of_le_one (show 0 ≤ p from zero_le) hp (show 1 ≤ 4 by decide)
  have ht6 : tau ^ 6 ≤ 1 := pow_le_one₀ zero_le htau
  calc
    u ≤ p ^ 4 * tau ^ 6 * n / 1536 := hinner
    _ ≤ p * 1 * n / 1536 := by gcongr
    _ = p * n / 1536 := by ring
    _ ≤ p * n / 8 := div_le_div_of_nonneg_left zero_le (by norm_num) (by norm_num)

theorem regularized_auxiliary_mass_normalization
    (n m : ℕ) (p tau tau0 : ℝ≥0) (htau0 : 0 < tau0) (htau : tau0 ≤ tau)
    (hmass : (p : ℝ) ^ 3 * tau * (n : ℝ) ^ 3 / 192 ≤ (m : ℝ)) :
    p ^ 3 * (n : ℝ≥0) ^ 3 / (192 / tau0) ≤ m := by
  have hbound : p ^ 3 * tau * (n : ℝ≥0) ^ 3 / 192 ≤ m := by exact_mod_cast hmass
  calc
    _ = p ^ 3 * tau0 * (n : ℝ≥0) ^ 3 / 192 := by
      field_simp
    _ ≤ p ^ 3 * tau * (n : ℝ≥0) ^ 3 / 192 := by gcongr
    _ ≤ _ := hbound

theorem inversePower_parameter_le_half
    (t e : ℕ) (ht : 2 ≤ t) (he : 1 ≤ e) : (1 / (t : ℝ≥0) ^ e) ≤ 1 / 2 := by
  have ht1 : (1 : ℝ≥0) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have ht2 : (2 : ℝ≥0) ≤ t := by exact_mod_cast ht
  exact (inversePower_parameter_le_one_div t e ht1 he).trans
    (one_div_le_one_div_of_le (by norm_num) ht2)

end Erdos207
