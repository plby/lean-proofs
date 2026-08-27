/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceSmallPrimes
import ErdosProblems.Erdos4b.FGKMTSourceScales

/-! # The source scales satisfy the exact rounded survivor-decomposition ranges -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem eventually_source_rounded_initial_ranges {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      ⌊sourceSmallPrimeLower x⌋₊ ≤ ⌊sourceSmallPrimeUpper a x⌋₊ ∧
      ⌊sourceSmallPrimeUpper a x⌋₊ ≤ x / 2 ∧
      ⌊sourceIntervalLength c x⌋₊ ≤ (x / 2) * ⌊sourceSmallPrimeLower x⌋₊ := by
  have hL := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_sourceSmallPrime_ranges ha, eventually_sourceIntervalLength_bounds hc,
    eventually_ge_atTop (4 : ℕ), hL.eventually_ge_atTop 2] with x hr hy hx hlog
  let v := sourceSmallPrimeLower x
  let V := ⌊v⌋₊
  have hv : 2 ≤ v := hr.1
  have hv0 : 0 ≤ v := by linarith
  have hV1 : 1 ≤ V := (Nat.le_floor_iff hv0).mpr (by
    norm_num only [Nat.cast_one]
    linarith)
  have hVhalf : v / 2 ≤ (V : ℝ) := by
    have hfloor : v < (V : ℝ) + 1 := Nat.lt_floor_add_one v
    have hV1R : (1 : ℝ) ≤ V := by exact_mod_cast hV1
    linarith
  have hhalf : (x : ℝ) / 4 ≤ (x / 2 : ℕ) := by
    have hn : x ≤ 4 * (x / 2) := by omega
    have hR : (x : ℝ) ≤ 4 * (x / 2 : ℕ) := by exact_mod_cast hn
    linarith
  have hpower : 8 * Real.log (x : ℝ) ^ 2 ≤ v := by
    have hp : (8 : ℝ) ≤ Real.log (x : ℝ) ^ 18 :=
      (by norm_num : (8 : ℝ) ≤ 2 ^ 18).trans
        (pow_le_pow_left₀ (by norm_num) hlog 18)
    calc
      _ ≤ Real.log (x : ℝ) ^ 2 * Real.log (x : ℝ) ^ 18 := by
        nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg (Real.log (x : ℝ)))]
      _ = v := by change _ = Real.log (x : ℝ) ^ 20; rw [← pow_add]
  refine ⟨Nat.floor_mono hr.2.1, ?_, ?_⟩
  · have hz : (⌊sourceSmallPrimeUpper a x⌋₊ : ℝ) ≤ (x : ℝ) / 2 :=
      (Nat.floor_le (Real.exp_pos _).le).trans hr.2.2.le
    have hn : ⌊sourceSmallPrimeUpper a x⌋₊ * 2 ≤ x := by
      exact_mod_cast (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hz
    omega
  · have hy0 : 0 ≤ sourceIntervalLength c x := (Nat.cast_nonneg x).trans hy.1
    have hY : (⌊sourceIntervalLength c x⌋₊ : ℝ) ≤
        ((x / 2 : ℕ) : ℝ) * (V : ℝ) := by
      calc
        _ ≤ (x : ℝ) * Real.log (x : ℝ) ^ 2 := (Nat.floor_le hy0).trans hy.2.1
        _ ≤ (x : ℝ) * v / 8 := by
          nlinarith [mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg x : (0 : ℝ) ≤ x)]
        _ = ((x : ℝ) / 4) * (v / 2) := by ring
        _ ≤ _ := mul_le_mul hhalf hVhalf (by positivity) (Nat.cast_nonneg _)
    exact_mod_cast hY

end

end Erdos4b.FGKMT
