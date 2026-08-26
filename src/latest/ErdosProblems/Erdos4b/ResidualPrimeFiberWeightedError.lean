/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.ResidualPrimeFiberWeighted

/-!
# Absorbing the weighted residual-fibre endpoint errors

A third-power logarithmic saving suffices for the pointwise proxy
bound. This estimate has no factor counting the cofactors.
-/

namespace Erdos4b

noncomputable section

theorem residualEndpointErrors_three_le
    {C V L : ℝ} {T z : ℕ} (hC : 0 ≤ C) (hV : 0 < V) (hL : 0 < L)
    (hLV : L ≤ V) (hlarge : 16 * C ≤ V) (hzT : z ≤ T)
    (hlogT : V / 2 ≤ Real.log T) (hlogz : V / 2 ≤ Real.log z) :
    C * T / Real.rpow (Real.log T) 3 + C * z / Real.rpow (Real.log z) 3 ≤
      (T : ℝ) / (V * L) := by
  have hhalf : 0 < V / 2 := half_pos hV
  have ht : 0 < Real.log T := hhalf.trans_le hlogT
  have hz : 0 < Real.log z := hhalf.trans_le hlogz
  have hpowT := pow_le_pow_left₀ hhalf.le hlogT 3
  have hpowz := pow_le_pow_left₀ hhalf.le hlogz 3
  have hzT' : (z : ℝ) ≤ T := by exact_mod_cast hzT
  have hpow : 0 < (V / 2) ^ (3 : ℕ) := pow_pos hhalf _
  rw [show Real.rpow (Real.log T) 3 = Real.log T ^ (3 : ℕ) by
      rw [← Real.rpow_natCast]; norm_num,
    show Real.rpow (Real.log z) 3 = Real.log z ^ (3 : ℕ) by
      rw [← Real.rpow_natCast]; norm_num]
  calc
    _ ≤ C * T / (V / 2) ^ 3 + C * z / (V / 2) ^ 3 :=
      add_le_add (div_le_div_of_nonneg_left (by positivity) hpow hpowT)
        (div_le_div_of_nonneg_left (by positivity) hpow hpowz)
    _ ≤ C * T / (V / 2) ^ 3 + C * T / (V / 2) ^ 3 :=
      add_le_add le_rfl (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hzT' hC) hpow.le)
    _ = (16 * C / V) * ((T : ℝ) / (V * V)) := by field_simp; ring
    _ ≤ 1 * ((T : ℝ) / (V * V)) :=
      mul_le_mul_of_nonneg_right ((div_le_one hV).mpr hlarge) (by positivity)
    _ = (T : ℝ) / (V * V) := one_mul _
    _ ≤ (T : ℝ) / (V * L) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hV hL)
        (mul_le_mul_of_nonneg_left hLV hV.le)

theorem residualWeightedMainTerm_le
    {C V L : ℝ} {T : ℕ} (hC : 0 ≤ C) (hV : 0 < V) (hL : 0 < L)
    (hlog : V / 2 ≤ Real.log T) :
    C * T / (Real.log T * L) ≤ 2 * C * T / (V * L) := by
  calc
    _ ≤ C * T / ((V / 2) * L) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos (half_pos hV) hL)
        (mul_le_mul_of_nonneg_right hlog hL.le)
    _ = _ := by ring

end

end Erdos4b
