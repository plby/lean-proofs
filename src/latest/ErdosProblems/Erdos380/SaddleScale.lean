import ErdosProblems.Erdos380.Core
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The elementary asymptotic scale

The integer base is the floor of `exp(sqrt(log N * log log N / 2) / 1000)`.
Using powers of this base will permit a finite subdivision of the prime
ranges, without a saddle-point theorem for smooth numbers.
-/

open Filter
open scoped Topology

namespace Erdos380

lemma log_floor_exp_sub_tendsto_zero {α : Type*} {l : Filter α} {f : α → ℝ}
    (hf : Tendsto f l atTop) :
    Tendsto (fun x => Real.log (⌊Real.exp (f x)⌋₊ : ℝ) - f x) l (𝓝 0) := by
  have he := Real.tendsto_exp_atTop.comp hf
  have hr := (tendsto_nat_floor_div_atTop (R := ℝ)).comp he
  have hl := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  rw [Real.log_one] at hl
  apply hl.congr'
  filter_upwards [hf.eventually (eventually_ge_atTop (0 : ℝ))] with x hx
  have hp : 0 < ⌊Real.exp (f x)⌋₊ := Nat.floor_pos.mpr (Real.one_le_exp hx)
  simp only [Function.comp_apply]
  rw [Real.log_div (by exact_mod_cast hp.ne') (Real.exp_ne_zero _), Real.log_exp]

lemma log_floor_exp_div_tendsto_one {α : Type*} {l : Filter α} {f : α → ℝ}
    (hf : Tendsto f l atTop) :
    Tendsto (fun x => Real.log (⌊Real.exp (f x)⌋₊ : ℝ) / f x) l (𝓝 1) := by
  have h := ((log_floor_exp_sub_tendsto_zero hf).div_atTop hf).add_const 1
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [hf.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  field_simp
  ring

noncomputable def saddleLog (N : ℕ) : ℝ :=
  Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) / 2) / 1000

noncomputable def scaleBase (N : ℕ) : ℕ := ⌊Real.exp (saddleLog N)⌋₊

lemma saddleLog_nonneg (N : ℕ) : 0 ≤ saddleLog N := by unfold saddleLog; positivity

lemma one_le_scaleBase (N : ℕ) : 1 ≤ scaleBase N :=
  Nat.floor_pos.mpr (Real.one_le_exp (saddleLog_nonneg N))

lemma log_nat_tendsto_atTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem saddleLog_tendsto_atTop : Tendsto saddleLog atTop atTop := by
  have hloglog := Real.tendsto_log_atTop.comp log_nat_tendsto_atTop
  exact (Real.tendsto_sqrt_atTop.comp
    ((log_nat_tendsto_atTop.atTop_mul_atTop₀ hloglog).atTop_div_const (by norm_num : (0 : ℝ) < 2))).atTop_div_const
      (by norm_num : (0 : ℝ) < 1000)

theorem scaleBase_tendsto_atTop : Tendsto scaleBase atTop atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp saddleLog_tendsto_atTop)

theorem log_scaleBase_div_saddleLog_tendsto_one :
    Tendsto (fun N => Real.log (scaleBase N : ℝ) / saddleLog N) atTop (𝓝 1) :=
  log_floor_exp_div_tendsto_one saddleLog_tendsto_atTop

lemma saddleLog_div_log_eq {N : ℕ} (hL : 0 < Real.log (N : ℝ)) :
    saddleLog N / Real.log N =
      Real.sqrt (Real.log (Real.log (N : ℝ)) / (2 * Real.log N)) / 1000 := by
  have heq : Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) / 2 =
      Real.log (N : ℝ) ^ 2 * (Real.log (Real.log (N : ℝ)) / (2 * Real.log N)) := by
    field_simp
  unfold saddleLog
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hL.le]
  field_simp

theorem saddleLog_div_log_tendsto_zero :
    Tendsto (fun N => saddleLog N / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp log_nat_tendsto_atTop
  have hh : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / (2 * Real.log N)) atTop (𝓝 0) := by
    convert hratio.div_const 2 using 1
    · funext N
      simp only [Function.comp_apply, id_eq]
      ring
    · norm_num
  have h := hh.sqrt.div_const 1000
  simp only [Real.sqrt_zero, zero_div] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hN
  exact (saddleLog_div_log_eq hN).symm

theorem log_scaleBase_div_log_tendsto_zero :
    Tendsto (fun N => Real.log (scaleBase N : ℝ) / Real.log (N : ℝ)) atTop (𝓝 0) := by
  have h := log_scaleBase_div_saddleLog_tendsto_one.mul saddleLog_div_log_tendsto_zero
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [saddleLog_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hN
  field_simp

theorem eventually_scaleBase_pow_le (a : ℕ) : ∀ᶠ N : ℕ in atTop, scaleBase N ^ a ≤ N := by
  have hr := log_scaleBase_div_log_tendsto_zero.const_mul (a : ℝ)
  simp only [mul_zero] at hr
  filter_upwards [hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop 1] with N hratio hlog hN
  have hnum : (a : ℝ) * Real.log (scaleBase N : ℝ) ≤ Real.log N := by
    have h' : (a : ℝ) * Real.log (scaleBase N : ℝ) / Real.log N ≤ 1 := by
      simpa only [mul_div_assoc] using hratio.le
    simpa only [one_mul] using (div_le_iff₀ hlog).mp h'
  have hreal : (scaleBase N : ℝ) ^ a ≤ N := by
    apply (Real.log_le_log_iff (by
      exact_mod_cast (pow_pos (show 0 < scaleBase N from lt_of_lt_of_le Nat.zero_lt_one (one_le_scaleBase N)) a))
      (by exact_mod_cast (by omega : 0 < N))).mp
    rwa [Real.log_pow]
  exact_mod_cast hreal

lemma loglog_nat_tendsto_atTop :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp log_nat_tendsto_atTop

lemma log_scaleBase_tendsto_atTop :
    Tendsto (fun N => Real.log (scaleBase N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp scaleBase_tendsto_atTop)

lemma saddleLog_sq {N : ℕ} (hL : 0 ≤ Real.log (N : ℝ))
    (hll : 0 ≤ Real.log (Real.log (N : ℝ))) :
    saddleLog N ^ 2 = Real.log N * Real.log (Real.log N) / 2000000 := by
  rw [saddleLog, div_pow, Real.sq_sqrt (by positivity)]
  norm_num
  ring

theorem log_saddleLog_div_loglog_tendsto_half :
    Tendsto (fun N => Real.log (saddleLog N) / Real.log (Real.log (N : ℝ))) atTop (𝓝 (1 / 2)) := by
  have hr : Tendsto (fun N : ℕ => Real.log (Real.log (Real.log (N : ℝ))) /
      Real.log (Real.log (N : ℝ))) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp loglog_nat_tendsto_atTop
  let c := Real.log 2 / 2 + Real.log 1000
  have hc : Tendsto (fun N : ℕ => c / Real.log (Real.log (N : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop loglog_nat_tendsto_atTop
  have h := ((hr.const_mul (1 / 2)).sub hc).const_add (1 / 2)
  norm_num only [mul_zero, sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with N hN
  have hL : 0 < Real.log (N : ℝ) := by linarith
  have hll : 0 < Real.log (Real.log (N : ℝ)) := Real.log_pos hN
  have hsqrt : 0 < Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) / 2) :=
    Real.sqrt_pos.mpr (by positivity)
  rw [saddleLog, Real.log_div hsqrt.ne' (by norm_num), Real.log_sqrt (by positivity),
    Real.log_div (mul_ne_zero hL.ne' hll.ne') (by norm_num), Real.log_mul hL.ne' hll.ne']
  dsimp [c]
  field_simp <;> ring

theorem loglog_scaleBase_sub_log_saddleLog_tendsto_zero :
    Tendsto (fun N => Real.log (Real.log (scaleBase N : ℝ)) - Real.log (saddleLog N)) atTop (𝓝 0) := by
  have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
    log_scaleBase_div_saddleLog_tendsto_one
  rw [Real.log_one] at h
  apply h.congr'
  filter_upwards [log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    saddleLog_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hS hf
  simp only [Function.comp_apply]
  exact Real.log_div hS.ne' hf.ne'

theorem loglog_scaleBase_div_loglog_tendsto_half :
    Tendsto (fun N => Real.log (Real.log (scaleBase N : ℝ)) / Real.log (Real.log (N : ℝ)))
      atTop (𝓝 (1 / 2)) := by
  have h := (loglog_scaleBase_sub_log_saddleLog_tendsto_zero.div_atTop loglog_nat_tendsto_atTop).add
    log_saddleLog_div_loglog_tendsto_half
  norm_num only [zero_add] at h
  convert h using 1
  funext N
  ring

/-- This is the scalar relation used in all logarithmic smooth-number
estimates; it is a limit of elementary functions, not an analytic-number-
theory input. -/
theorem scaleBase_saddle_relation :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) * Real.log (Real.log (scaleBase N : ℝ)) /
      Real.log (scaleBase N : ℝ) ^ 2) atTop (𝓝 1000000) := by
  have hinv := log_scaleBase_div_saddleLog_tendsto_one.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simp only [inv_div, inv_one] at hinv
  have h := (loglog_scaleBase_div_loglog_tendsto_half.mul (hinv.pow 2)).const_mul 2000000
  norm_num only [one_pow, mul_one] at h
  have h' : Tendsto (fun N => (2000000 : ℝ) *
      (Real.log (Real.log (scaleBase N : ℝ)) / Real.log (Real.log (N : ℝ)) *
        (saddleLog N / Real.log (scaleBase N : ℝ)) ^ 2)) atTop (𝓝 1000000) := by
    convert h using 1 <;> norm_num
  apply h'.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ)),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hN hS
  have hL : 0 ≤ Real.log (N : ℝ) := by linarith
  have hll : 0 < Real.log (Real.log (N : ℝ)) := Real.log_pos hN
  rw [div_pow, saddleLog_sq hL hll.le]
  field_simp

theorem loglog_div_log_scaleBase_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (scaleBase N : ℝ)) atTop (𝓝 0) := by
  have hinv := loglog_scaleBase_div_loglog_tendsto_half.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  simp only [inv_div] at hinv
  have hslow : Tendsto (fun N => Real.log (Real.log (scaleBase N : ℝ)) /
      Real.log (scaleBase N : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp log_scaleBase_tendsto_atTop
  have h := hinv.mul hslow
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with N hN
  have hp : 0 < Real.log (Real.log (scaleBase N : ℝ)) := Real.log_pos hN
  field_simp

theorem eventually_log_pow_le_scaleBase (a : ℕ) : ∀ᶠ N : ℕ in atTop,
    Real.log (N : ℝ) ^ a ≤ scaleBase N := by
  have hr := loglog_div_log_scaleBase_tendsto_zero.const_mul (a : ℝ)
  simp only [mul_zero] at hr
  filter_upwards [hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    log_scaleBase_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    log_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hratio hS hL
  have hnum : (a : ℝ) * Real.log (Real.log (N : ℝ)) ≤ Real.log (scaleBase N : ℝ) := by
    have h' : (a : ℝ) * Real.log (Real.log (N : ℝ)) / Real.log (scaleBase N : ℝ) ≤ 1 := by
      simpa only [mul_div_assoc] using hratio.le
    simpa only [one_mul] using (div_le_iff₀ hS).mp h'
  apply (Real.log_le_log_iff (pow_pos hL a) (by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_scaleBase N)))).mp
  rwa [Real.log_pow]

theorem saddleLog_loglog_div_log_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) * saddleLog N / Real.log N) atTop (𝓝 0) := by
  have hraw := (isLittleO_log_rpow_rpow_atTop (s := 1) 3 (by norm_num)).tendsto_div_nhds_zero.comp
    log_nat_tendsto_atTop
  have hr : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ 3 / Real.log N) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_ofNat, Real.rpow_one] using hraw
  have h := (hr.div_const 2000000).sqrt
  simp only [zero_div, Real.sqrt_zero] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))] with N hN
  have hL : 0 < Real.log (N : ℝ) := by linarith
  have hll : 0 ≤ Real.log (Real.log (N : ℝ)) := (Real.log_pos hN).le
  have hsq : (Real.log (Real.log (N : ℝ)) * saddleLog N / Real.log N) ^ 2 =
      Real.log (Real.log (N : ℝ)) ^ 3 / Real.log N / 2000000 := by
    rw [div_pow, mul_pow, saddleLog_sq hL.le hll]
    field_simp <;> ring
  rw [← hsq, Real.sqrt_sq (div_nonneg (mul_nonneg hll (saddleLog_nonneg N)) hL.le)]

theorem loglog_mul_log_scaleBase_div_log_tendsto_zero :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) * Real.log (scaleBase N : ℝ) / Real.log N)
      atTop (𝓝 0) := by
  have h := saddleLog_loglog_div_log_tendsto_zero.mul log_scaleBase_div_saddleLog_tendsto_one
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [saddleLog_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with N hN
  field_simp

/-- The coefficient left by harmonic neighbor counting tends to zero. -/
theorem scaleBase_error_coefficient_tendsto_zero :
    Tendsto (fun N : ℕ => (1 + Real.log (Real.log (N : ℝ))) *
      Real.log (scaleBase N : ℝ) / Real.log N) atTop (𝓝 0) := by
  have h := log_scaleBase_div_log_tendsto_zero.add loglog_mul_log_scaleBase_div_log_tendsto_zero
  simp only [add_zero] at h
  convert h using 1
  funext N
  ring

end Erdos380
