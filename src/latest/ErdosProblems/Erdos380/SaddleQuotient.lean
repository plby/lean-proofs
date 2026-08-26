import ErdosProblems.Erdos380.LowerCost

/-! # Uniform smoothness parameters below a fixed power of the scale -/

open Filter
open scoped Topology

namespace Erdos380

noncomputable def saddleQuotient (k c N : ℕ) : ℝ :=
  (Real.log (N : ℝ) - c * Real.log (scaleBase N : ℝ)) /
    (k * Real.log (scaleBase N : ℝ))

theorem saddleQuotient_ratio {k : ℕ} (hk : 0 < k) (c : ℕ) :
    Tendsto (fun N => saddleQuotient k c N / lowerSmoothParameter N)
      atTop (𝓝 (1000 / k)) := by
  have hX := lowerSmoothExponent_ratio.inv₀ (by positivity : (1 / Real.log 2 : ℝ) ≠ 0)
  simp only [inv_div, div_one] at hX
  have hsmall := (log_scaleBase_div_log_tendsto_zero.const_mul (c : ℝ)).const_sub 1
  simp only [mul_zero, sub_zero] at hsmall
  have h := ((lowerPrimeExponent_ratio.mul hX).mul hsmall).div_const (k : ℝ)
  have hc : (1000 / Real.log 2 * Real.log 2 * 1) / (k : ℝ) = 1000 / k := by
    rw [div_mul_cancel₀ _ log_two_pos.ne', mul_one]
  rw [hc] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    lowerPrimeExponent_tendsto_atTop.eventually (eventually_ge_atTop 1),
    lowerSmoothExponent_tendsto_atTop.eventually (eventually_ge_atTop 1)] with N hL hS hY hX
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hYR : (lowerPrimeExponent N : ℝ) ≠ 0 := by exact_mod_cast (by omega : lowerPrimeExponent N ≠ 0)
  have hXR : (lowerSmoothExponent N : ℝ) ≠ 0 := by exact_mod_cast (by omega : lowerSmoothExponent N ≠ 0)
  dsimp [saddleQuotient, lowerSmoothParameter]
  field_simp

theorem saddleQuotient_tendsto_atTop {k : ℕ} (hk : 0 < k) (c : ℕ) :
    Tendsto (saddleQuotient k c) atTop atTop :=
  tendsto_atTop_of_pos_ratio (by positivity) (saddleQuotient_ratio hk c) lowerSmoothParameter_tendsto_atTop

theorem log_saddleQuotient_ratio {k : ℕ} (hk : 0 < k) (c : ℕ) :
    Tendsto (fun N => Real.log (saddleQuotient k c N) / Real.log (Real.log (scaleBase N : ℝ)))
      atTop (𝓝 1) := by
  have h₁ := log_ratio_tendsto_one_of_ratio (by positivity : (0 : ℝ) < 1000 / k)
    (saddleQuotient_ratio hk c) lowerSmoothParameter_tendsto_atTop
  have h := h₁.mul log_lowerSmoothParameter_div_loglog_scaleBase
  rw [one_mul] at h
  apply h.congr'
  filter_upwards [lowerSmoothParameter_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
    with N hN
  have hp := Real.log_pos hN
  field_simp

theorem saddleQuotient_log_cost {k : ℕ} (hk : 0 < k) (c : ℕ) :
    Tendsto (fun N => saddleQuotient k c N * Real.log (saddleQuotient k c N) /
      Real.log (scaleBase N : ℝ)) atTop (𝓝 (1000000 / k)) := by
  have hsmall := (log_scaleBase_div_log_tendsto_zero.const_mul (c : ℝ)).const_sub 1
  simp only [mul_zero, sub_zero] at hsmall
  have h := ((hsmall.mul scaleBase_saddle_relation).mul (log_saddleQuotient_ratio hk c)).div_const (k : ℝ)
  simp only [one_mul, mul_one] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with N hL hS1
  have hS : 0 < Real.log (scaleBase N : ℝ) := by linarith
  have hls := Real.log_pos hS1
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  dsimp [saddleQuotient]
  field_simp

theorem log_saddleQuotient_div_log_scaleBase {k : ℕ} (hk : 0 < k) (c : ℕ) :
    Tendsto (fun N => Real.log (saddleQuotient k c N) / Real.log (scaleBase N : ℝ))
      atTop (𝓝 0) := by
  have hslow := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp log_scaleBase_tendsto_atTop
  have h := (log_saddleQuotient_ratio hk c).mul hslow
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with N hN
  have hp := Real.log_pos hN
  simp only [Function.comp_apply, id_eq]
  field_simp

theorem loglog_scaleBase_pow_div_log_saddleQuotient {k : ℕ} (hk : 0 < k) (c : ℕ) :
    Tendsto (fun N => Real.log (Real.log (scaleBase N ^ k : ℕ)) /
      Real.log (saddleQuotient k c N)) atTop (𝓝 1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hloglog := Real.tendsto_log_atTop.comp log_scaleBase_tendsto_atTop
  have hconst : Tendsto (fun N => Real.log (k : ℝ) / Real.log (Real.log (scaleBase N : ℝ)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hloglog
  have hnum := hconst.add_const 1
  rw [zero_add] at hnum
  have h := hnum.div (log_saddleQuotient_ratio hk c) (by norm_num : (1 : ℝ) ≠ 0)
  rw [div_one] at h
  apply h.congr'
  filter_upwards [log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with N hS1
  have hS : 0 < Real.log (scaleBase N : ℝ) := by linarith
  have hls := Real.log_pos hS1
  simp only [Pi.div_apply, Nat.cast_pow, Real.log_pow, Real.log_mul hkR.ne' hS.ne']
  field_simp

end Erdos380
