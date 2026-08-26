/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.ResidualDyadicParameters
import ErdosProblems.Erdos4b.GeneralFourierSourceCutoffGrowth

/-!
# The logarithmic scales on the saved dyadic parameter ray

The companion-to-ambient ratio tends to zero, while the companion scale
still exceeds the Fourier three-quarter-power lower bound.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped Topology

def dyadicAmbientScale (a r : ℕ) : ℝ := Real.log (primaryFrontier a r)

def dyadicCompanionScale (r : ℕ) : ℝ := Real.log (smoothFrontier r)

def sourcePreSieveCutoff (r : ℕ) : ℕ := r / 100

theorem dyadicAmbientScale_eq (a r : ℕ) :
    dyadicAmbientScale a r = (primaryExponent a r : ℝ) * Real.log 2 := by
  simp only [dyadicAmbientScale, primaryFrontier, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem dyadicCompanionScale_eq (r : ℕ) :
    dyadicCompanionScale r = (smoothExponent r : ℝ) * Real.log 2 := by
  simp only [dyadicCompanionScale, smoothFrontier, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

theorem two_le_dyadicCore (r : ℕ) : 2 ≤ core r := by
  unfold core
  have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ))
    (show 1 ≤ 2 ^ r from Nat.one_le_two_pow)
  simpa only [pow_one] using h

theorem one_le_dyadicAmbientScale (a r : ℕ) : 1 ≤ dyadicAmbientScale a r := by
  have hE : 2 ≤ primaryExponent a r :=
    (two_le_dyadicCore r).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hEr : (2 : ℝ) ≤ primaryExponent a r := by exact_mod_cast hE
  rw [dyadicAmbientScale_eq]
  nlinarith [half_le_log_two]

theorem dyadicCompanionScale_pos {r : ℕ} (hr : 0 < r) : 0 < dyadicCompanionScale r := by
  rw [dyadicCompanionScale_eq]
  exact mul_pos (by exact_mod_cast Nat.mul_pos hr (rankinDenominator_pos r))
    (Real.log_pos (by norm_num))

theorem primaryExponent_eq_rankin_mul (a r : ℕ) :
    primaryExponent a r = 2 ^ (a + r) * rankinDenominator r := by
  unfold primaryExponent rankinDenominator
  rw [show a + 2 * r = (a + r) + r by omega, pow_add, mul_assoc]

theorem dyadicCompanionScale_div_ambient (a r : ℕ) :
    dyadicCompanionScale r / dyadicAmbientScale a r = (r : ℝ) / (2 : ℝ) ^ (a + r) := by
  have hB : (rankinDenominator r : ℝ) ≠ 0 := by exact_mod_cast (rankinDenominator_pos r).ne'
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  rw [dyadicCompanionScale_eq, dyadicAmbientScale_eq, primaryExponent_eq_rankin_mul]
  simp only [smoothExponent, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem tendsto_dyadicCompanionScale_div_ambient_zero (a : ℕ) :
    Tendsto (fun r ↦ dyadicCompanionScale r / dyadicAmbientScale a r) atTop (𝓝 0) := by
  have hb : Tendsto (fun r : ℕ ↦ (r : ℝ) / (2 : ℝ) ^ r) atTop (𝓝 0) := by
    simpa only [pow_one] using tendsto_pow_const_div_const_pow_of_one_lt 1
      (by norm_num : (1 : ℝ) < 2)
  have h := hb.div_const ((2 : ℝ) ^ a)
  simp only [zero_div] at h
  apply h.congr
  intro r
  rw [dyadicCompanionScale_div_ambient, div_div, pow_add, mul_comm ((2 : ℝ) ^ r)]

theorem tendsto_dyadicAmbientScale_atTop (a : ℕ) :
    Tendsto (dyadicAmbientScale a) atTop atTop := by
  have hlow : ∀ r : ℕ, (r : ℝ) * Real.log 2 ≤ dyadicAmbientScale a r := by
    intro r
    rw [dyadicAmbientScale_eq]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast self_le_primaryExponent a r)
      (Real.log_nonneg (by norm_num))
  apply tendsto_atTop_mono hlow
  simpa only [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))

theorem dyadicSmoothExponent_fourth_le {a r : ℕ}
    (hr : 1 ≤ r) (hexp : 3 * a + 2 * r + 8 ≤ 2 ^ r) :
    256 * primaryExponent a r ^ 3 ≤ smoothExponent r ^ 4 := by
  have hE : primaryExponent a r = 2 ^ (a + 2 * r + 2 ^ r) := by
    unfold primaryExponent core
    exact (pow_add 2 (a + 2 * r) (2 ^ r)).symm
  have hS : smoothExponent r = r * 2 ^ (r + 2 ^ r) := by
    unfold smoothExponent rankinDenominator core
    rw [pow_add]
  rw [hE, hS, mul_pow, ← pow_mul, ← pow_mul,
    show (256 : ℕ) = 2 ^ 8 by norm_num, ← pow_add]
  calc
    _ ≤ 2 ^ ((r + 2 ^ r) * 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)

theorem dyadicCompanionScale_threeQuarter_lower {a r : ℕ}
    (hr : 1 ≤ r) (hexp : 3 * a + 2 * r + 8 ≤ 2 ^ r) :
    2 * (dyadicAmbientScale a r + 1) ^ (3 / 4 : ℝ) ≤ dyadicCompanionScale r := by
  let V := dyadicAmbientScale a r
  let L := dyadicCompanionScale r
  have hV : 1 ≤ V := one_le_dyadicAmbientScale a r
  have hL : 0 < L := dyadicCompanionScale_pos (by omega)
  have hE : 0 ≤ (primaryExponent a r : ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hnat : 256 * (primaryExponent a r : ℝ) ^ 3 ≤ (smoothExponent r : ℝ) ^ 4 := by
    exact_mod_cast dyadicSmoothExponent_fourth_le hr hexp
  have hpow : 128 * V ^ 3 ≤ L ^ 4 := by
    calc
      _ = 128 * (primaryExponent a r : ℝ) ^ 3 * Real.log 2 ^ 3 := by
        dsimp [V]; rw [dyadicAmbientScale_eq, mul_pow]; ring
      _ ≤ 256 * (primaryExponent a r : ℝ) ^ 3 * Real.log 2 ^ 4 := by
        have h := mul_le_mul_of_nonneg_left half_le_log_two
          (show 0 ≤ 256 * (primaryExponent a r : ℝ) ^ 3 * Real.log 2 ^ 3 by positivity)
        nlinarith [h]
      _ ≤ (smoothExponent r : ℝ) ^ 4 * Real.log 2 ^ 4 :=
        mul_le_mul_of_nonneg_right hnat (by positivity)
      _ = _ := by dsimp [L]; rw [dyadicCompanionScale_eq, mul_pow]
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hL.le
  have hq : ((V + 1) ^ (3 / 4 : ℝ)) ^ 4 = (V + 1) ^ 3 := by
    rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ V + 1)]
    norm_num
  change (2 * (V + 1) ^ (3 / 4 : ℝ)) ^ 4 ≤ L ^ 4
  rw [mul_pow, hq]
  have hcube := pow_le_pow_left₀ (by linarith : 0 ≤ V + 1) (show V + 1 ≤ 2 * V by linarith) 3
  nlinarith [hcube]

theorem eventually_dyadicCompanionScale_threeQuarter_lower (a : ℕ) :
    ∀ᶠ r in atTop, 2 * (dyadicAmbientScale a r + 1) ^ (3 / 4 : ℝ) ≤ dyadicCompanionScale r := by
  filter_upwards [eventually_ge_atTop (3 * a + 8), eventually_ge_atTop 4] with r hra hr4
  exact dyadicCompanionScale_threeQuarter_lower (by omega)
    ((show 3 * a + 2 * r + 8 ≤ 3 * r by omega).trans (three_mul_le_two_pow hr4))

end

end Erdos4b.SmoothParameters
