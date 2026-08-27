import ErdosProblems.Erdos4.TiltedParameters

/-! The logarithmic cutoff and signed-offset range satisfy the geometric sieve requirements. -/

namespace Erdos4.Tilted

open Filter FGKMT

theorem eventually_smallCutoff_bounds :
    ∀ᶠ x : ℕ in atTop,
      2 ≤ smallCutoff x ∧ smallCutoff x ≤ sieveCutoff x ∧
      Real.log (x : ℝ) ^ (98 : ℕ) ≤ (smallCutoff x : ℝ) ∧
      (smallCutoff x : ℝ) ≤ Real.log (x : ℝ) ^ (100 : ℕ) ∧
      (smallCutoff x : ℝ) ^ (4 : ℕ) ≤ (x : ℝ) ∧
      Real.log (Real.log (x : ℝ)) ≤ Real.log (smallCutoff x : ℝ) ∧
      Real.log (smallCutoff x : ℝ) ≤ 100 * Real.log (Real.log (x : ℝ)) ∧
      64 * Real.log (x : ℝ) ≤ (smallCutoff x : ℝ) := by
  filter_upwards [log_tendsto.eventually (eventually_ge_atTop 64),
    eventually_const_log_power_le_rpow 100 128 (by norm_num : (0 : ℝ) < 1),
    eventually_const_log_power_le_rpow 400 1 (by norm_num : (0 : ℝ) < 1)]
    with x hL h100 h400
  let L := Real.log (x : ℝ)
  change 64 ≤ L at hL
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hlow : L ^ (98 : ℕ) ≤ (smallCutoff x : ℝ) := floor_cutoff_ge_pow (by linarith)
  have hupp : (smallCutoff x : ℝ) ≤ L ^ (100 : ℕ) := Nat.floor_le (by positivity)
  have h128 : 128 * (smallCutoff x : ℝ) ≤ (x : ℝ) := by
    have hh := (mul_le_mul_of_nonneg_left hupp (by norm_num : (0 : ℝ) ≤ 128)).trans
      (by simpa only [Real.rpow_one] using h100)
    exact hh
  have hwB : smallCutoff x ≤ sieveCutoff x := by
    have hh : 128 * smallCutoff x ≤ x := by exact_mod_cast h128
    unfold sieveCutoff
    omega
  have hLL : L ≤ L ^ (98 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (98 : ℕ))
  have hLw : L ≤ (smallCutoff x : ℝ) := hLL.trans hlow
  have hw2 : 2 ≤ smallCutoff x := by
    have hh : (2 : ℝ) ≤ smallCutoff x := by linarith
    exact_mod_cast hh
  have hwpow : (smallCutoff x : ℝ) ^ (4 : ℕ) ≤ (x : ℝ) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (smallCutoff x)) hupp 4
    rw [← pow_mul] at hh
    exact hh.trans (by simpa only [one_mul, Real.rpow_one] using h400)
  have hloglo : Real.log L ≤ Real.log (smallCutoff x : ℝ) := Real.log_le_log hLpos hLw
  have hloghi : Real.log (smallCutoff x : ℝ) ≤ 100 * Real.log L := by
    have hh := Real.log_le_log (by exact_mod_cast (show 0 < smallCutoff x by omega)) hupp
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hlarge : 64 * L ≤ (smallCutoff x : ℝ) := by
    have hL2 : L ^ 2 ≤ L ^ (98 : ℕ) := pow_le_pow_right₀ hL1 (by norm_num)
    have hh : 64 * L ≤ L ^ 2 := by nlinarith
    exact (hh.trans hL2).trans hlow
  exact ⟨hw2, hwB, hlow, hupp, hwpow, hloglo, hloghi, hlarge⟩

theorem offsetLimit_bounds {x : ℕ} (hL : 1 ≤ Real.log (x : ℝ)) :
    Real.log (x : ℝ) < (offsetLimit x : ℝ) ∧
      (offsetLimit x : ℝ) ≤ 2 * Real.log (x : ℝ) := by
  have hf := Nat.lt_floor_add_one (Real.log (x : ℝ))
  have hu := Nat.floor_le (Real.log_natCast_nonneg x)
  simp only [offsetLimit, Nat.cast_add, Nat.cast_one]
  exact ⟨hf, by linarith⟩

theorem sieve_width_of_cutoff {x Y w : ℕ} (hL : 0 < Real.log (x : ℝ))
    (hY : (Y : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ))
    (hw : 64 * Real.log (x : ℝ) ≤ (w : ℝ)) : Y < (sieveCutoff x + 1) * w := by
  have hxq : (x : ℝ) < 64 * ((sieveCutoff x + 1 : ℕ) : ℝ) := by
    have hh : x < 64 * (sieveCutoff x + 1) := by unfold sieveCutoff; omega
    exact_mod_cast hh
  have hh : (Y : ℝ) < (((sieveCutoff x + 1) * w : ℕ) : ℝ) := by
    calc
      _ ≤ (x : ℝ) * Real.log (x : ℝ) := hY
      _ < (64 * ((sieveCutoff x + 1 : ℕ) : ℝ)) * Real.log (x : ℝ) := mul_lt_mul_of_pos_right hxq hL
      _ = ((sieveCutoff x + 1 : ℕ) : ℝ) * (64 * Real.log (x : ℝ)) := by ring
      _ ≤ ((sieveCutoff x + 1 : ℕ) : ℝ) * (w : ℝ) :=
        mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)
      _ = _ := (Nat.cast_mul _ _).symm
  exact_mod_cast hh

theorem color_offset_width {x Y p : ℕ} (hx : 0 < x) (hxp : x ≤ p)
    (hY : (Y : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ)) : Y < p * offsetLimit x := by
  have hU : Real.log (x : ℝ) < (offsetLimit x : ℝ) := by
    simpa only [offsetLimit, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (Real.log (x : ℝ))
  have hh : (Y : ℝ) < ((p * offsetLimit x : ℕ) : ℝ) := by
    calc
      _ ≤ (x : ℝ) * Real.log (x : ℝ) := hY
      _ < (x : ℝ) * (offsetLimit x : ℝ) := mul_lt_mul_of_pos_left hU (Nat.cast_pos.mpr hx)
      _ ≤ (p : ℝ) * (offsetLimit x : ℝ) := mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hxp) (Nat.cast_nonneg _)
      _ = _ := (Nat.cast_mul _ _).symm
  exact_mod_cast hh

end Erdos4.Tilted
