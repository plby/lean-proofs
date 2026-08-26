import ErdosProblems.Erdos421.DivisorWindowMajorant

/-! # A fixed power-saving range for the type-I estimate -/

namespace Erdos421

theorem divisor_window_majorant_power_bound {X M Y C : ℝ}
    (hX : 1 ≤ X) (hlog : 1 ≤ Real.log X) (hM0 : 0 ≤ M)
    (hM : M ≤ X ^ (21 / 40 : ℝ)) (hY : X ^ (1 / 10 : ℝ) ≤ Y) :
    32 * C ^ 2 * (X + 512 * M ^ 2 * Real.log X) * (Real.log X) ^ 3 / Y +
      8 * C ^ 2 / X ^ 3 ≤ 20000 * C ^ 2 * X ^ (19 / 20 : ℝ) * (Real.log X) ^ 4 := by
  have hXp : 0 < X := by linarith
  have hL : 0 ≤ Real.log X := by linarith
  have hQ : 0 < X ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hXp _
  have hYp : 0 < Y := hQ.trans_le hY
  have hP : 0 ≤ X ^ (21 / 20 : ℝ) := Real.rpow_nonneg hXp.le _
  have hM2 : M ^ 2 ≤ X ^ (21 / 20 : ℝ) := by
    calc
      _ ≤ (X ^ (21 / 40 : ℝ)) ^ 2 := pow_le_pow_left₀ hM0 hM 2
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXp.le]
        norm_num
  have hXP : X ≤ X ^ (21 / 20 : ℝ) :=
    Real.self_le_rpow_of_one_le hX (by norm_num)
  have hPL : X ^ (21 / 20 : ℝ) ≤ X ^ (21 / 20 : ℝ) * Real.log X :=
    le_mul_of_one_le_right hP hlog
  have hpref : X + 512 * M ^ 2 * Real.log X ≤ 513 * X ^ (21 / 20 : ℝ) * Real.log X := by
    have hb := mul_le_mul_of_nonneg_right hM2 hL
    linarith
  have hmain : 32 * C ^ 2 * (X + 512 * M ^ 2 * Real.log X) * (Real.log X) ^ 3 / Y ≤
      16416 * C ^ 2 * X ^ (19 / 20 : ℝ) * (Real.log X) ^ 4 := by
    calc
      _ ≤ 32 * C ^ 2 * (513 * X ^ (21 / 20 : ℝ) * Real.log X) * (Real.log X) ^ 3 / Y := by
        apply div_le_div_of_nonneg_right _ hYp.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpref (by positivity)) (by positivity)
      _ ≤ 32 * C ^ 2 * (513 * X ^ (21 / 20 : ℝ) * Real.log X) * (Real.log X) ^ 3 /
          X ^ (1 / 10 : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hQ hY
      _ = 16416 * C ^ 2 * (X ^ (21 / 20 : ℝ) / X ^ (1 / 10 : ℝ)) * (Real.log X) ^ 4 := by ring
      _ = _ := by
        rw [← Real.rpow_sub hXp]
        norm_num
  have hR1 : (1 : ℝ) ≤ X ^ (19 / 20 : ℝ) := Real.one_le_rpow hX (by norm_num)
  have hL4 : (1 : ℝ) ≤ (Real.log X) ^ 4 := one_le_pow₀ hlog
  have hX3 : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ hX
  have htail : 8 * C ^ 2 / X ^ 3 ≤ 8 * C ^ 2 * X ^ (19 / 20 : ℝ) * (Real.log X) ^ 4 := by
    calc
      _ ≤ 8 * C ^ 2 / 1 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hX3
      _ = 8 * C ^ 2 := div_one _
      _ ≤ 8 * C ^ 2 * X ^ (19 / 20 : ℝ) := le_mul_of_one_le_right (by positivity) hR1
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hL4
  have hb := add_le_add hmain htail
  have hn : 0 ≤ C ^ 2 * X ^ (19 / 20 : ℝ) * (Real.log X) ^ 4 := by positivity
  nlinarith

end Erdos421
