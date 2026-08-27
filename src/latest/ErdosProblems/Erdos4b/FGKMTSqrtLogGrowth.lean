/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Polynomial and square-root-log exponential comparisons

Every exponent is fixed before the endpoint tends to infinity. These scalar
lemmas absorb the explicit Vaughan losses without a varying-exponent theorem.
-/

namespace Erdos4b.FGKMT

open Filter

theorem eventually_log_pow_le_exp_mul_sqrtLog (j : ℕ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x : ℕ in atTop, Real.log (x : ℝ) ^ j ≤
      Real.exp (b * Real.sqrt (Real.log (x : ℝ))) := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have huTop := Real.tendsto_sqrt_atTop.comp hlogTop
  have hdom := ((isLittleO_pow_exp_pos_mul_atTop (2 * j) hb).comp_tendsto huTop).eventuallyLE
  filter_upwards [hdom] with x hx
  have hlog0 := Real.log_natCast_nonneg x
  have hpow : Real.sqrt (Real.log (x : ℝ)) ^ (2 * j) = Real.log (x : ℝ) ^ j := by
    rw [pow_mul, Real.sq_sqrt hlog0]
  simp only [Function.comp_apply, Real.norm_eq_abs, hpow] at hx
  simpa only [abs_of_nonneg (pow_nonneg hlog0 j), abs_of_pos (Real.exp_pos _)] using hx

theorem eventually_exp_mul_sqrtLog_le_rpow (d : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x : ℕ in atTop, Real.exp (d * Real.sqrt (Real.log (x : ℝ))) ≤ (x : ℝ) ^ b := by
  have hlogTop : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have huTop := Real.tendsto_sqrt_atTop.comp hlogTop
  filter_upwards [huTop.eventually (eventually_ge_atTop (d / b)),
    eventually_ge_atTop (1 : ℕ)] with x hx hx1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have hu0 := Real.sqrt_nonneg (Real.log (x : ℝ))
  have husq := Real.sq_sqrt (Real.log_natCast_nonneg x)
  have hdu : d ≤ b * Real.sqrt (Real.log (x : ℝ)) := by
    simpa only [Function.comp_apply, mul_comm] using (div_le_iff₀ hb).mp hx
  have hscaled := mul_le_mul_of_nonneg_right hdu hu0
  rw [Real.rpow_def_of_pos hxpos]
  exact Real.exp_monotone (by nlinarith)

theorem eventually_rpow_log_pow_le_expDecay (beta d : ℝ) (j : ℕ) (hbeta : beta < 1) :
    ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ beta * Real.log (x : ℝ) ^ j ≤
      (x : ℝ) * Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) := by
  let b : ℝ := (1 - beta) / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hlogdom := ((isLittleO_log_rpow_rpow_atTop (j : ℝ) hb).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  have hexpdom := eventually_exp_mul_sqrtLog_le_rpow d hb
  filter_upwards [hlogdom, hexpdom, eventually_ge_atTop (1 : ℕ)] with x hlog hexp hx1
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx1
  have hlog0 := Real.log_natCast_nonneg x
  simp only [Function.comp_apply, Real.norm_eq_abs, Real.rpow_natCast,
    abs_of_nonneg (pow_nonneg hlog0 j),
    abs_of_nonneg (Real.rpow_nonneg hxpos.le b)] at hlog
  have hproduct : ((x : ℝ) ^ beta * Real.log (x : ℝ) ^ j) *
      Real.exp (d * Real.sqrt (Real.log (x : ℝ))) ≤ x := by
    calc
      _ ≤ ((x : ℝ) ^ beta * (x : ℝ) ^ b) * (x : ℝ) ^ b :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hxpos.le _)) hexp
          (Real.exp_pos _).le (by positivity)
      _ = (x : ℝ) := by
        rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos,
          show beta + b + b = 1 by dsimp [b]; ring, Real.rpow_one]
  calc
    _ ≤ (x : ℝ) / Real.exp (d * Real.sqrt (Real.log (x : ℝ))) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr hproduct
    _ = _ := by simp only [div_eq_mul_inv, neg_mul, Real.exp_neg]

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_log_pow_le_exp_mul_sqrtLog
#print axioms Erdos4b.FGKMT.eventually_rpow_log_pow_le_expDecay
