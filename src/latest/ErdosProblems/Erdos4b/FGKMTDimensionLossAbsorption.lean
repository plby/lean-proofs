/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTDimensionLogLoss

/-!
# Uniform absorption of cubic dimension losses

The endpoint threshold is chosen before every dimension k below log(x)^0.1.
The comparison also covers the quadratic coefficient/Cauchy loss.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem eventually_rpow_dimensionScale_le_sqrtLog {H e : ℝ} (hH : 0 < H) (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop,
      H * Real.log (x : ℝ) ^ (3 / 10 : ℝ) * dimensionLogLossScale x ≤
        e * Real.sqrt (Real.log (x : ℝ)) := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp_tendsto
    hlogTop).def (by positivity : 0 < e / (3 * H))
  filter_upwards [hsmall, hlogTop.eventually (eventually_ge_atTop (2 : ℝ)),
    (Real.tendsto_log_atTop.comp hlogTop).eventually (eventually_ge_atTop (1 : ℝ))] with
      x hsmall hL hlogL
  let L := Real.log (x : ℝ)
  have hL2 : 2 ≤ L := hL
  have hLpos : 0 < L := by linarith
  have hlogL1 : 1 ≤ Real.log L := hlogL
  have hscale : dimensionLogLossScale x ≤ 3 * Real.log L := by
    have harg : 1 + L ≤ L ^ 2 := by nlinarith
    have h := Real.log_le_log (by linarith : 0 < 1 + L) harg
    rw [Real.log_pow] at h
    change 1 + Real.log (1 + L) ≤ _
    norm_num at h
    linarith
  have hsmall' : Real.log L ≤ e / (3 * H) * L ^ (1 / 5 : ℝ) := by
    change ‖Real.log L‖ ≤ e / (3 * H) * ‖L ^ (1 / 5 : ℝ)‖ at hsmall
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ Real.log L),
      abs_of_nonneg (Real.rpow_nonneg hLpos.le (1 / 5))] using hsmall
  calc
    _ ≤ H * L ^ (3 / 10 : ℝ) * (3 * Real.log L) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ ≤ H * L ^ (3 / 10 : ℝ) * (3 * (e / (3 * H) * L ^ (1 / 5 : ℝ))) := by gcongr
    _ = e * (L ^ (3 / 10 : ℝ) * L ^ (1 / 5 : ℝ)) := by field_simp
    _ = _ := by
      rw [← Real.rpow_add hLpos, show (3 / 10 : ℝ) + 1 / 5 = 1 / 2 by norm_num]
      change e * L ^ (1 / 2 : ℝ) = e * Real.sqrt L
      rw [Real.sqrt_eq_rpow]

theorem cube_le_log_rpow_of_dimension {x k : ℕ}
    (hk : (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ)) :
    (k : ℝ) ^ 3 ≤ Real.log (x : ℝ) ^ (3 / 10 : ℝ) := by
  have hL := Real.log_natCast_nonneg x
  calc
    _ ≤ (Real.log (x : ℝ) ^ (1 / 10 : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg k) hk 3
    _ = (Real.log (x : ℝ) ^ (1 / 10 : ℝ)) ^ ((3 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ 3).symm
    _ = _ := by rw [← Real.rpow_mul hL]; norm_num

theorem eventually_uniform_cubeDimension_loss {H e : ℝ} (hH : 0 < H) (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop, ∀ k : ℕ,
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
        H * (k : ℝ) ^ 3 * dimensionLogLossScale x ≤ e * Real.sqrt (Real.log (x : ℝ)) := by
  filter_upwards [eventually_rpow_dimensionScale_le_sqrtLog hH he] with x hx
  intro k hk
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (cube_le_log_rpow_of_dimension hk) hH.le)
      (zero_le_one.trans (one_le_dimensionLogLossScale x))).trans hx

theorem eventually_uniform_squareDimension_loss {H e : ℝ} (hH : 0 < H) (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop, ∀ k : ℕ, 1 ≤ k →
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
        H * (k : ℝ) ^ 2 * dimensionLogLossScale x ≤ e * Real.sqrt (Real.log (x : ℝ)) := by
  filter_upwards [eventually_uniform_cubeDimension_loss hH he] with x hx
  intro k hk1 hk
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hpow : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := pow_le_pow_right₀ hkR (by omega)
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hH.le)
    (zero_le_one.trans (one_le_dimensionLogLossScale x))).trans (hx k hk)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_uniform_cubeDimension_loss
#print axioms Erdos4b.FGKMT.eventually_uniform_squareDimension_loss
