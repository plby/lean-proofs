import ErdosProblems.Erdos587.CriticalScale

/-! Power-scale estimates for removing the common factor in one step. -/

namespace Erdos587

lemma common_factor_quarter_scale {T g : ℝ} (hT : 0 < T) (hg : 0 < g) :
    (T / g ^ 2) ^ (1 / 4 : ℝ) = T ^ (1 / 4 : ℝ) / Real.sqrt g := by
  rw [Real.div_rpow hT.le (sq_nonneg g), ← Real.rpow_natCast_mul hg.le 2 (1 / 4 : ℝ)]
  norm_num
  rw [← Real.sqrt_eq_rpow]

lemma common_factor_threequarter_scale {T g : ℝ} (hT : 0 < T) (hg : 0 < g) :
    (T / g ^ 2) ^ (3 / 4 : ℝ) = T ^ (3 / 4 : ℝ) / (g * Real.sqrt g) := by
  rw [Real.div_rpow hT.le (sq_nonneg g), ← Real.rpow_natCast_mul hg.le 2 (3 / 4 : ℝ)]
  have heq : ((2 : ℕ) : ℝ) * (3 / 4) = 1 + 1 / 2 := by norm_num
  rw [heq, Real.rpow_add hg, Real.rpow_one, ← Real.sqrt_eq_rpow]

lemma quarter_power_sq {T : ℝ} (hT : 0 ≤ T) : (T ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt T := by
  rw [← Real.rpow_mul_natCast hT]
  norm_num
  rw [← Real.sqrt_eq_rpow]

lemma threequarter_power_sq {T : ℝ} (hT : 0 < T) :
    (T ^ (3 / 4 : ℝ)) ^ 2 = T * Real.sqrt T := by
  rw [← Real.rpow_mul_natCast hT.le]
  have heq : (3 / 4 : ℝ) * (2 : ℕ) = 1 + 1 / 2 := by norm_num
  rw [heq, Real.rpow_add hT, Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem common_factor_first_width_budget {T g H J W : ℝ}
    (hT : 0 < T) (hg : 0 < g) (hH : 0 < H) (hJ : 0 < J) (hJH : J ≤ H) (hW : 0 ≤ W)
    (hproper : g * (H * J) ≤ T) (hprod : T ^ (3 / 4 : ℝ) * W ≤ H * J) :
    (T / g ^ 2) ^ (1 / 4 : ℝ) * W ≤ H / g := by
  have hV : 0 < H * J := mul_pos hH hJ
  have hroot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hprodSq := pow_le_pow_left₀ (by positivity : 0 ≤ T ^ (3 / 4 : ℝ) * W) hprod 2
  rw [mul_pow, threequarter_power_sq hT] at hprodSq
  have hscaled := mul_le_mul_of_nonneg_right hproper (show 0 ≤ Real.sqrt T * W ^ 2 by positivity)
  have hsmall : g * Real.sqrt T * W ^ 2 ≤ H * J := by
    apply (mul_le_mul_iff_left₀ hV).mp
    nlinarith
  have hHsq : g * Real.sqrt T * W ^ 2 ≤ H ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hJH hH.le
    nlinarith
  have hcandidateSq : (T ^ (1 / 4 : ℝ) * Real.sqrt g * W) ^ 2 ≤ H ^ 2 := by
    rw [mul_pow, mul_pow, quarter_power_sq hT.le, Real.sq_sqrt hg.le]
    nlinarith
  have hcandidate : T ^ (1 / 4 : ℝ) * Real.sqrt g * W ≤ H := by
    have hh := Real.sqrt_le_sqrt hcandidateSq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq hH.le] at hh
  rw [common_factor_quarter_scale hT hg]
  apply (le_div_iff₀ hg).mpr
  have heq : (T ^ (1 / 4 : ℝ) / Real.sqrt g * W) * g =
      T ^ (1 / 4 : ℝ) * Real.sqrt g * W := by
    calc
      _ = (T ^ (1 / 4 : ℝ) * W) * (g / Real.sqrt g) := by ring
      _ = _ := by rw [Real.div_sqrt]; ring
  rwa [heq]

theorem common_factor_axis_width_budget {T g V W : ℝ}
    (hT : 0 < T) (hg : 1 ≤ g) (hW : 0 ≤ W)
    (hprod : T ^ (3 / 4 : ℝ) * W ≤ V) :
    (T / g ^ 2) ^ (1 / 4 : ℝ) * W ≤ V / Real.sqrt T := by
  have hgpos : 0 < g := by linarith
  have hroot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hscale : T / g ^ 2 ≤ T := (div_le_self hT.le (by nlinarith))
  have hpower := Real.rpow_le_rpow (div_nonneg hT.le (sq_nonneg g)) hscale
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  apply (mul_le_mul_of_nonneg_right hpower hW).trans
  apply (le_div_iff₀ hroot).mpr
  have heq : (T ^ (1 / 4 : ℝ) * W) * Real.sqrt T = T ^ (3 / 4 : ℝ) * W := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = (T ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ)) * W := by ring
      _ = _ := by rw [← Real.rpow_add hT]; norm_num
  rwa [heq]

theorem common_factor_volume_budget {T g V W : ℝ}
    (hT : 0 < T) (hg : 1 ≤ g) (hW : 0 ≤ W)
    (hprod : T ^ (3 / 4 : ℝ) * W ≤ V) :
    (T / g ^ 2) ^ (3 / 4 : ℝ) * W ≤ V / g := by
  have hgpos : 0 < g := by linarith
  have hroot1 : 1 ≤ Real.sqrt g := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hg
  rw [common_factor_threequarter_scale hT hgpos]
  calc
    _ ≤ (T ^ (3 / 4 : ℝ) / g) * W := by gcongr; nlinarith
    _ = (T ^ (3 / 4 : ℝ) * W) / g := by ring
    _ ≤ V / g := div_le_div_of_nonneg_right hprod hgpos.le

theorem common_factor_width_ratio {T g H J W : ℝ}
    (hT : 0 < T) (hH : 0 < H) (hJ : 0 < J) (hW : 0 ≤ W) (_hg : 0 ≤ g)
    (hproper : g * (H * J) ≤ T)
    (hside : T ^ (1 / 4 : ℝ) * W ≤ J) (hprod : T ^ (3 / 4 : ℝ) * W ≤ H * J) :
    g * W ^ 2 ≤ J := by
  have hmul := mul_le_mul hside hprod (by positivity : 0 ≤ T ^ (3 / 4 : ℝ) * W) hJ.le
  have heq : (T ^ (1 / 4 : ℝ) * W) * (T ^ (3 / 4 : ℝ) * W) = T * W ^ 2 := by
    calc
      _ = (T ^ (1 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) * W ^ 2 := by ring
      _ = _ := by rw [← Real.rpow_add hT]; norm_num
  rw [heq] at hmul
  have hscaled := mul_le_mul_of_nonneg_right hproper (sq_nonneg W)
  apply (mul_le_mul_iff_left₀ (mul_pos hH hJ)).mp
  nlinarith

end Erdos587
