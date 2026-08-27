import ErdosProblems.Erdos4.FGKMTExceptionalDecay

/-! Uniform absorption of logarithmic factors into exponential error savings. -/

namespace Erdos4.FGKMT

open Filter Asymptotics

theorem sqrtLog_tendsto_atTop :
    Tendsto (fun x : ℕ => Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem eventually_sqrtLog_pow_le_exp (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop, Real.sqrt (Real.log (x : ℝ)) ^ m ≤
      Real.exp (a * Real.sqrt (Real.log (x : ℝ))) := by
  have hh := ((isLittleO_pow_exp_pos_mul_atTop m ha).comp_tendsto sqrtLog_tendsto_atTop).eventuallyLE
  filter_upwards [hh] with x hx
  simpa only [Function.comp_apply, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) m), abs_of_pos (Real.exp_pos _)] using hx

theorem eventually_const_mul_sqrtLog_pow_le_exp (m : ℕ) (C : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop, C * Real.sqrt (Real.log (x : ℝ)) ^ m ≤
      Real.exp (a * Real.sqrt (Real.log (x : ℝ))) := by
  have hh := (((isLittleO_pow_exp_pos_mul_atTop m ha).const_mul_left C).comp_tendsto
    sqrtLog_tendsto_atTop).eventuallyLE
  filter_upwards [hh] with x hx
  have hnorm : |C * Real.sqrt (Real.log (x : ℝ)) ^ m| ≤
      Real.exp (a * Real.sqrt (Real.log (x : ℝ))) := by
    simpa only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hx
  exact (le_abs_self _).trans hnorm

theorem eventually_rpow_sqrtLog_pow_le_decay {α β c : ℝ} (hαβ : α < β) (m : ℕ) :
    ∀ᶠ x : ℕ in atTop, (x : ℝ) ^ α * Real.sqrt (Real.log (x : ℝ)) ^ m ≤
      (x : ℝ) ^ β * Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) := by
  have hdom := eventually_sqrtLog_pow_le_exp m (by norm_num : (0 : ℝ) < 1)
  have hlarge := sqrtLog_tendsto_atTop.eventually (eventually_ge_atTop ((c + 1) / (β - α)))
  filter_upwards [hdom, hlarge, eventually_ge_atTop 1] with x hpoly hlarge hx
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlog : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  let u := Real.sqrt (Real.log (x : ℝ))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have husq : u ^ 2 = Real.log (x : ℝ) := Real.sq_sqrt hlog
  have hlinear : c + 1 ≤ (β - α) * u := by
    have hh := (div_le_iff₀ (sub_pos.mpr hαβ)).mp hlarge
    nlinarith
  have hquad := mul_le_mul_of_nonneg_right hlinear hu
  calc
    _ ≤ (x : ℝ) ^ α * Real.exp u := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hxpos.le α)
      simpa only [one_mul] using hpoly
    _ = Real.exp (Real.log (x : ℝ) * α + u) := by
      rw [Real.rpow_def_of_pos hxpos, ← Real.exp_add]
    _ ≤ Real.exp (Real.log (x : ℝ) * β - c * u) := by
      apply Real.exp_le_exp.mpr
      rw [← husq]
      nlinarith
    _ = _ := by
      rw [Real.rpow_def_of_pos hxpos, ← Real.exp_add]
      congr 1
      ring

end Erdos4.FGKMT
