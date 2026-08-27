/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceReservePowerFailure

/-! # Attainable integer supply, incidence, left-loss, and stopping cutoffs -/

namespace Erdos207

open scoped NNReal

theorem internal_cover_rounded_budgets (mu : ℝ≥0) (hmu : 512 ≤ mu) :
    let supply := ⌊mu / 8⌋₊
    let degree := ⌊mu / 256⌋₊
    let leftCap := ⌈mu / 128⌉₊
    let threshold := ⌊mu / 32⌋₊
    0 < threshold ∧ mu / 64 ≤ threshold ∧ mu / 512 ≤ degree ∧
      4 * degree + leftCap + threshold ≤ supply ∧ (supply : ℝ≥0) ≤ mu / 8 := by
  dsimp only
  have hsupply := Nat.lt_floor_add_one (mu / 8)
  have hdegree := Nat.floor_le (show (0 : ℝ≥0) ≤ mu / 256 from zero_le)
  have hdegree' := Nat.lt_floor_add_one (mu / 256)
  have hthreshold := Nat.floor_le (show (0 : ℝ≥0) ≤ mu / 32 from zero_le)
  have hthreshold' := Nat.lt_floor_add_one (mu / 32)
  have hleft := Nat.ceil_lt_add_one (show (0 : ℝ≥0) ≤ mu / 128 from zero_le)
  have hmuR : (512 : ℝ) ≤ mu := by exact_mod_cast hmu
  have hsR : (mu : ℝ) / 8 < (⌊mu / 8⌋₊ : ℝ) + 1 := by exact_mod_cast hsupply
  have hdR : (⌊mu / 256⌋₊ : ℝ) ≤ (mu : ℝ) / 256 := by exact_mod_cast hdegree
  have hdR' : (mu : ℝ) / 256 < (⌊mu / 256⌋₊ : ℝ) + 1 := by exact_mod_cast hdegree'
  have htR : (⌊mu / 32⌋₊ : ℝ) ≤ (mu : ℝ) / 32 := by exact_mod_cast hthreshold
  have htR' : (mu : ℝ) / 32 < (⌊mu / 32⌋₊ : ℝ) + 1 := by exact_mod_cast hthreshold'
  have hlR : (⌈mu / 128⌉₊ : ℝ) < (mu : ℝ) / 128 + 1 := by exact_mod_cast hleft
  refine ⟨?_, ?_, ?_, ?_, Nat.floor_le zero_le⟩
  · have : (0 : ℝ) < (⌊mu / 32⌋₊ : ℝ) := by linarith only [hmuR, htR']
    exact_mod_cast this
  · apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
    linarith only [hmuR, htR']
  · apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_div, NNReal.coe_ofNat, NNReal.coe_natCast]
    linarith only [hmuR, hdR']
  · have : 4 * (⌊mu / 256⌋₊ : ℝ) + (⌈mu / 128⌉₊ : ℝ) + (⌊mu / 32⌋₊ : ℝ) ≤ (⌊mu / 8⌋₊ : ℝ) := by
      linarith only [hmuR,hsR,hdR,htR,hlR]
    exact_mod_cast this

theorem internal_cover_rounded_left_and_point
    (p r eta u epsilon : ℝ≥0) (hmu : 512 ≤ r ^ 2 * p ^ 2 * eta * u) (hepsilon : 128 * epsilon ≤ eta) :
    epsilon * p ^ 2 * r ^ 2 * u ≤ (⌈r ^ 2 * p ^ 2 * eta * u / 128⌉₊ : ℝ≥0) ∧
      ((⌊r ^ 2 * p ^ 2 * eta * u / 32⌋₊ : ℝ≥0))⁻¹ ≤ 64 / (r ^ 2 * p ^ 2 * eta * u) := by
  have hmu0 : 0 < r ^ 2 * p ^ 2 * eta * u := (by norm_num : (0 : ℝ≥0) < 512).trans_le hmu
  have ht := (internal_cover_rounded_budgets (r ^ 2 * p ^ 2 * eta * u) hmu).2.1
  constructor
  · apply le_trans _ (Nat.le_ceil (r ^ 2 * p ^ 2 * eta * u / 128))
    apply (le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 128)).mpr
    calc
      _ = (128 * epsilon) * (r ^ 2 * p ^ 2 * u) := by ring
      _ ≤ eta * (r ^ 2 * p ^ 2 * u) := mul_le_mul_of_nonneg_right hepsilon zero_le
      _ = _ := by ring
  · have hb := one_div_le_one_div_of_le (div_pos hmu0 (by norm_num)) ht
    simpa only [one_div, inv_div, inv_inv] using hb

end Erdos207
