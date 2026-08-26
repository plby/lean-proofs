import ErdosProblems.Erdos380.ScalarRatios

/-! # Integer exponents for the singleton lower bound -/

open Filter
open scoped Topology

namespace Erdos380

noncomputable def lowerTotalExponent (N : ℕ) : ℕ :=
  ⌊(1 / Real.log 2) * Real.log (N : ℝ)⌋₊

noncomputable def lowerPrimeExponent (N : ℕ) : ℕ :=
  ⌊(1000 / Real.log 2) * Real.log (scaleBase N : ℝ)⌋₊

noncomputable def lowerSmoothExponent (N : ℕ) : ℕ :=
  lowerTotalExponent N - 2 * (lowerPrimeExponent N + 1)

noncomputable def lowerSmoothParameter (N : ℕ) : ℝ :=
  (lowerSmoothExponent N : ℝ) / lowerPrimeExponent N

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem lowerTotalExponent_ratio :
    Tendsto (fun N : ℕ => (lowerTotalExponent N : ℝ) / Real.log N)
      atTop (𝓝 (1 / Real.log 2)) :=
  nat_floor_scaled_ratio_tendsto log_nat_tendsto_atTop (by positivity)

theorem lowerPrimeExponent_ratio :
    Tendsto (fun N : ℕ => (lowerPrimeExponent N : ℝ) / Real.log (scaleBase N : ℝ))
      atTop (𝓝 (1000 / Real.log 2)) :=
  nat_floor_scaled_ratio_tendsto log_scaleBase_tendsto_atTop (by positivity)

theorem lowerPrimeExponent_div_log_tendsto_zero :
    Tendsto (fun N : ℕ => (lowerPrimeExponent N : ℝ) / Real.log N) atTop (𝓝 0) := by
  have h := lowerPrimeExponent_ratio.mul log_scaleBase_div_log_tendsto_zero
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
    with N hN
  field_simp

theorem lowerExponent_padding_ratio :
    Tendsto (fun N : ℕ => (2 * (lowerPrimeExponent N + 1) : ℝ) / Real.log N)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun N : ℕ => (1 : ℝ) / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_nat_tendsto_atTop
  have h := (lowerPrimeExponent_div_log_tendsto_zero.add hc).const_mul 2
  norm_num only [add_zero, mul_zero] at h
  convert h using 1
  funext N
  ring

theorem eventually_lowerExponent_padding_le : ∀ᶠ N : ℕ in atTop,
    2 * (lowerPrimeExponent N + 1) ≤ lowerTotalExponent N := by
  have h := lowerTotalExponent_ratio.sub lowerExponent_padding_ratio
  rw [sub_zero] at h
  filter_upwards [h.eventually (lt_mem_nhds (by positivity : (0 : ℝ) < 1 / Real.log 2)),
    log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hratio hL
  have hlt := (div_lt_div_iff_of_pos_right hL).mp (sub_pos.mp hratio)
  have hnat : 2 * (lowerPrimeExponent N + 1) < lowerTotalExponent N := by exact_mod_cast hlt
  exact hnat.le

theorem lowerSmoothExponent_ratio :
    Tendsto (fun N : ℕ => (lowerSmoothExponent N : ℝ) / Real.log N)
      atTop (𝓝 (1 / Real.log 2)) := by
  have h := lowerTotalExponent_ratio.sub lowerExponent_padding_ratio
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_lowerExponent_padding_le] with N hN
  rw [lowerSmoothExponent, Nat.cast_sub hN]
  push_cast
  ring

theorem lowerPrimeExponent_tendsto_atTop : Tendsto lowerPrimeExponent atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  exact tendsto_atTop_of_pos_ratio (by positivity) lowerPrimeExponent_ratio log_scaleBase_tendsto_atTop

theorem lowerSmoothExponent_tendsto_atTop : Tendsto lowerSmoothExponent atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  exact tendsto_atTop_of_pos_ratio (by positivity) lowerSmoothExponent_ratio log_nat_tendsto_atTop

theorem log_lowerSmoothExponent_ratio :
    Tendsto (fun N : ℕ => Real.log (lowerSmoothExponent N : ℝ) / Real.log (Real.log N))
      atTop (𝓝 1) :=
  log_ratio_tendsto_one_of_ratio (by positivity) lowerSmoothExponent_ratio log_nat_tendsto_atTop

theorem log_lowerPrimeExponent_ratio :
    Tendsto (fun N : ℕ => Real.log (lowerPrimeExponent N : ℝ) / Real.log (Real.log N))
      atTop (𝓝 (1 / 2)) := by
  have h₁ := log_ratio_tendsto_one_of_ratio (by positivity : (0 : ℝ) < 1000 / Real.log 2)
    lowerPrimeExponent_ratio log_scaleBase_tendsto_atTop
  have h := h₁.mul loglog_scaleBase_div_loglog_tendsto_half
  rw [one_mul] at h
  apply h.congr'
  filter_upwards [log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))]
    with N hN
  have hp := Real.log_pos hN
  field_simp

theorem log_lowerSmoothParameter_ratio :
    Tendsto (fun N : ℕ => Real.log (lowerSmoothParameter N) / Real.log (Real.log N))
      atTop (𝓝 (1 / 2)) := by
  have h := log_lowerSmoothExponent_ratio.sub log_lowerPrimeExponent_ratio
  have h' : Tendsto (fun N : ℕ =>
      Real.log (lowerSmoothExponent N : ℝ) / Real.log (Real.log N) -
        Real.log (lowerPrimeExponent N : ℝ) / Real.log (Real.log N)) atTop (𝓝 (1 / 2)) := by
    convert h using 1 <;> norm_num
  apply h'.congr'
  filter_upwards [lowerSmoothExponent_tendsto_atTop.eventually (eventually_ge_atTop 1),
    lowerPrimeExponent_tendsto_atTop.eventually (eventually_ge_atTop 1)] with N hX hY
  have hX0 : (lowerSmoothExponent N : ℝ) ≠ 0 := by exact_mod_cast (by omega : lowerSmoothExponent N ≠ 0)
  have hY0 : (lowerPrimeExponent N : ℝ) ≠ 0 := by exact_mod_cast (by omega : lowerPrimeExponent N ≠ 0)
  rw [lowerSmoothParameter, Real.log_div hX0 hY0]
  ring

theorem lowerSmoothParameter_tendsto_atTop : Tendsto lowerSmoothParameter atTop atTop := by
  have hlog := tendsto_atTop_of_pos_ratio (by norm_num : (0 : ℝ) < 1 / 2)
    log_lowerSmoothParameter_ratio loglog_nat_tendsto_atTop
  have h := Real.tendsto_exp_atTop.comp hlog
  apply h.congr'
  filter_upwards [lowerSmoothExponent_tendsto_atTop.eventually (eventually_ge_atTop 1),
    lowerPrimeExponent_tendsto_atTop.eventually (eventually_ge_atTop 1)] with N hX hY
  have hXpos : (0 : ℝ) < lowerSmoothExponent N := by exact_mod_cast (by omega : 0 < lowerSmoothExponent N)
  have hYpos : (0 : ℝ) < lowerPrimeExponent N := by exact_mod_cast (by omega : 0 < lowerPrimeExponent N)
  exact Real.exp_log (div_pos hXpos hYpos)

theorem log_lowerSmoothParameter_div_loglog_scaleBase :
    Tendsto (fun N : ℕ => Real.log (lowerSmoothParameter N) / Real.log (Real.log (scaleBase N : ℝ)))
      atTop (𝓝 1) := by
  have h := log_lowerSmoothParameter_ratio.div loglog_scaleBase_div_loglog_tendsto_half
    (by norm_num : (1 / 2 : ℝ) ≠ 0)
  rw [div_self (by norm_num : (1 / 2 : ℝ) ≠ 0)] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with N hN
  have hp := Real.log_pos hN
  simp only [Pi.div_apply]
  field_simp

end Erdos380
