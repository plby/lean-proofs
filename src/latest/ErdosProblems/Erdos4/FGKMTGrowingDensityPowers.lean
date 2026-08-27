import ErdosProblems.Erdos4.FGKMTOuterDensity
import ErdosProblems.Erdos4.FGKMTGrowingLogWeight

/-! Powers of the inverse initial density remain smaller than every fixed endpoint power. -/

namespace Erdos4.FGKMT

open Filter

theorem eventually_growing_log_dimension_power {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop,
      Real.log (x : ℝ) ^ (6 * sieveDimension (growingIndex x)) ≤ (x : ℝ) ^ a := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_growingDimension_bounds,
    growingDimension_tendsto.eventually (eventually_ge_atTop 3),
    eventually_growing_log_weight (by norm_num : (0 : ℝ) < 1),
    hlog.eventually (eventually_ge_atTop 1),
    sqrtLog_tendsto_atTop.eventually (eventually_ge_atTop (1 / (4 * a))),
    eventually_ge_atTop 1] with x hdim hk3 hweight hL hroot hx
  let L := Real.log (x : ℝ)
  let k := sieveDimension (growingIndex x)
  let u := Real.sqrt L
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL1
  have hu : 0 ≤ u := Real.sqrt_nonneg L
  have husq : u ^ 2 = L := Real.sq_sqrt hL0
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hkbound : (k : ℝ) ≤ L ^ (1 / 8 : ℝ) := by
    apply hdim.2.trans
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (1 / 100 : ℝ) ≤ 1 / 8)
  have hexp := hweight k x le_rfl hkbound
  have hdegree : 6 * k ≤ 2 * k ^ 2 := by change 3 ≤ k at hk3; nlinarith
  have hquarter : (1 / 4 : ℝ) ≤ a * u := by
    change 1 / (4 * a) ≤ u at hroot
    have hh := (div_le_iff₀ (by positivity : 0 < 4 * a)).mp hroot
    nlinarith
  have hquadratic := mul_le_mul_of_nonneg_right hquarter hu
  calc
    _ ≤ (1 + L) ^ (6 * k) := pow_le_pow_left₀ hL0 (by linarith) _
    _ ≤ (1 + L) ^ (2 * k ^ 2) := pow_le_pow_right₀ (by linarith) hdegree
    _ ≤ Real.exp (u / 4) := by simpa only [div_eq_mul_inv, one_mul, mul_comm, u, L] using hexp
    _ ≤ (x : ℝ) ^ a := by
      rw [Real.rpow_def_of_pos hxpos]
      apply Real.exp_le_exp.mpr
      change u / 4 ≤ L * a
      nlinarith

theorem eventually_growing_random_inverse_power {a : ℝ} (ha : 0 < a) :
    ∀ᶠ x : ℕ in atTop,
      1 / UnitFourier.unitDensity (growingRandomValue x) ^
        (3 * sieveDimension (growingIndex x)) ≤ (x : ℝ) ^ a := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_growing_random_density_lower, eventually_growing_log_dimension_power ha,
    hlog.eventually (eventually_ge_atTop 1)] with x hσ hpower hL
  let L := Real.log (x : ℝ)
  let k := sieveDimension (growingIndex x)
  let σ := UnitFourier.unitDensity (growingRandomValue x)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hσpos : 0 < σ := UnitFourier.unitDensity_pos (growingRandomValue x)
  have hinv : σ⁻¹ ≤ L ^ (2 : ℕ) := by
    have hh := one_div_le_one_div_of_le (by positivity : 0 < 1 / L ^ (2 : ℕ)) hσ
    simpa only [one_div, inv_inv, σ] using hh
  change 1 / σ ^ (3 * k) ≤ (x : ℝ) ^ a
  calc
    _ = (σ⁻¹) ^ (3 * k) := by simp only [one_div, inv_pow]
    _ ≤ (L ^ (2 : ℕ)) ^ (3 * k) := pow_le_pow_left₀ (inv_nonneg.mpr hσpos.le) hinv _
    _ = L ^ (6 * k) := by rw [← pow_mul]; congr 1; omega
    _ ≤ _ := hpower

end Erdos4.FGKMT
