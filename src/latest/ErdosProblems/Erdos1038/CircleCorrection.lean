import ErdosProblems.Erdos1038.CircleSinc
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The nonnegative self-gap in the circle block inequality

This file formalizes the scalar correction

`h(X) = log (2π) - 3/2 + 2 ∫₀¹ (1-t) log (sinc (Xt)) dt`

and proves its endpoint normalization and monotonicity on `(0, π]`.
-/

open Set Filter Interval MeasureTheory
open scoped Topology

namespace Erdos1038

noncomputable section

def circleCorrectionIntegrand (X t : ℝ) : ℝ :=
  (1 - t) * Real.log (Real.sinc (X * t))

def circleCorrection (X : ℝ) : ℝ :=
  Real.log (2 * Real.pi) - 3 / 2 +
    2 * ∫ t in (0 : ℝ)..1, circleCorrectionIntegrand X t

lemma intervalIntegrable_mul_log_zero_one :
    IntervalIntegrable (fun t : ℝ ↦ t * Real.log t) volume 0 1 := by
  exact intervalIntegral.intervalIntegrable_log'.continuousOn_mul
    continuousOn_id

lemma integral_mul_log_zero_one :
    (∫ t : ℝ in 0..1, t * Real.log t) = -(1 / 4 : ℝ) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := fun t : ℝ ↦ t ^ 2 / 2 * Real.log t - t ^ 2 / 4)
    (fa := 0) (fb := -(1 / 4 : ℝ))
    (hint := intervalIntegrable_mul_log_zero_one)]
  · norm_num
  · norm_num
  · intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    convert! (((hasDerivAt_pow 2 t).div_const 2).mul
      (Real.hasDerivAt_log ht0)).sub ((hasDerivAt_pow 2 t).div_const 4) using 1
    field_simp [ht0]
    ring
  · have hlogpow := tendsto_log_mul_rpow_nhdsGT_zero
      (show (0 : ℝ) < 2 by norm_num)
    have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hpow : Tendsto (fun t : ℝ ↦ t ^ 2) (𝓝[>] 0) (𝓝 0) := by
      simpa using! hid.pow 2
    have hfirst : Tendsto (fun t : ℝ ↦ t ^ 2 / 2 * Real.log t)
        (𝓝[>] 0) (𝓝 0) := by
      convert! hlogpow.const_mul (1 / 2 : ℝ) using 1
      · funext t
        rw [Real.rpow_two]
        ring
      · norm_num
    have hsecond : Tendsto (fun t : ℝ ↦ t ^ 2 / 4)
        (𝓝[>] 0) (𝓝 0) := by
      simpa using! hpow.div_const 4
    simpa using! hfirst.sub hsecond
  · have hc : ContinuousAt
        (fun t : ℝ ↦ t ^ 2 / 2 * Real.log t - t ^ 2 / 4) 1 :=
      (((continuousAt_id.pow 2).div_const 2).mul
        (Real.continuousAt_log (by norm_num))).sub
        ((continuousAt_id.pow 2).div_const 4)
    simpa using! tendsto_nhdsWithin_of_tendsto_nhds hc.tendsto

lemma integral_one_sub_mul_log_zero_one :
    (∫ t : ℝ in 0..1, (1 - t) * Real.log t) = -(3 / 4 : ℝ) := by
  rw [show (fun t : ℝ ↦ (1 - t) * Real.log t) =
      fun t ↦ Real.log t - t * Real.log t by
        funext t
        ring]
  rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_log'
    intervalIntegrable_mul_log_zero_one,
    integral_log, integral_mul_log_zero_one]
  norm_num

lemma log_sinc_mul_eventuallyEq {X : ℝ} (hX : 0 < X) :
    (fun t : ℝ ↦ Real.log (Real.sin (X * t)) - Real.log X - Real.log t) =ᶠ[
      codiscrete ℝ] (fun t ↦ Real.log (Real.sinc (X * t))) := by
  have htid : (fun t : ℝ ↦ t) ⁻¹' {0}ᶜ ∈ codiscrete ℝ := by
    apply analyticOnNhd_id.preimage_zero_mem_codiscrete
      (x := 1)
    simp
  have hsinzero : (fun t : ℝ ↦ Real.sin (X * t)) ⁻¹' {0}ᶜ ∈ codiscrete ℝ := by
    have hana : AnalyticOnNhd ℝ (fun t : ℝ ↦ Real.sin (X * t)) univ :=
      fun _ _ ↦ by fun_prop
    apply hana.preimage_zero_mem_codiscrete
      (x := (Real.pi / 2) / X)
    have harg : X * ((Real.pi / 2) / X) = Real.pi / 2 := by
      field_simp [hX.ne']
    rw [harg]
    simp
  filter_upwards [htid, hsinzero] with t ht hsin_t
  have ht0 : t ≠ 0 := by simpa using! ht
  have hXt0 : X * t ≠ 0 := mul_ne_zero hX.ne' ht0
  rw [Real.sinc_of_ne_zero hXt0, Real.log_div hsin_t hXt0,
    Real.log_mul hX.ne' ht0]
  ring

lemma codiscreteWithin_uIoc_le_codiscrete (a b : ℝ) :
    codiscreteWithin (Ι a b) ≤ codiscrete ℝ := by
  change codiscreteWithin (Ι a b) ≤ codiscreteWithin univ
  exact Filter.codiscreteWithin_mono (subset_univ _)

lemma intervalIntegrable_log_sinc_mul {X : ℝ} (hX : 0 < X) :
    IntervalIntegrable (fun t : ℝ ↦ Real.log (Real.sinc (X * t)))
      volume 0 1 := by
  have hsin : IntervalIntegrable
      (fun t : ℝ ↦ Real.log (Real.sin (X * t))) volume 0 1 := by
    have h := (intervalIntegrable_log_sin (a := (0 : ℝ)) (b := X)).comp_mul_left
      (c := X)
    simpa [Function.comp_apply, hX.ne'] using! h
  have hrhs : IntervalIntegrable
      (fun t : ℝ ↦ Real.log (Real.sin (X * t)) - Real.log X - Real.log t)
      volume 0 1 :=
    (hsin.sub intervalIntegrable_const).sub
      intervalIntegral.intervalIntegrable_log'
  exact hrhs.congr_codiscreteWithin
    ((log_sinc_mul_eventuallyEq hX).filter_mono
      (codiscreteWithin_uIoc_le_codiscrete 0 1))

lemma intervalIntegrable_circleCorrectionIntegrand {X : ℝ} (hX : 0 < X) :
    IntervalIntegrable (circleCorrectionIntegrand X) volume 0 1 := by
  exact (intervalIntegrable_log_sinc_mul hX).continuousOn_mul
    (by fun_prop : ContinuousOn (fun t : ℝ ↦ 1 - t) [[0, 1]])

theorem circleCorrection_antitoneOn :
    AntitoneOn circleCorrection (Ioc (0 : ℝ) Real.pi) := by
  intro X hX Y hY hXY
  have hmono :
      (∫ t in (0 : ℝ)..1, circleCorrectionIntegrand Y t) ≤
        ∫ t in (0 : ℝ)..1, circleCorrectionIntegrand X t := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo (show (0 : ℝ) ≤ 1 by norm_num)
      (intervalIntegrable_circleCorrectionIntegrand hY.1)
      (intervalIntegrable_circleCorrectionIntegrand hX.1)
    intro t ht
    have hXtpi : X * t < Real.pi := calc
      X * t ≤ Real.pi * t := mul_le_mul_of_nonneg_right hX.2 ht.1.le
      _ < Real.pi * 1 := mul_lt_mul_of_pos_left ht.2 Real.pi_pos
      _ = Real.pi := mul_one _
    have hYtpi : Y * t < Real.pi := calc
      Y * t ≤ Real.pi * t := mul_le_mul_of_nonneg_right hY.2 ht.1.le
      _ < Real.pi * 1 := mul_lt_mul_of_pos_left ht.2 Real.pi_pos
      _ = Real.pi := mul_one _
    have hXt : X * t ∈ Icc (0 : ℝ) Real.pi := by
      exact ⟨(mul_pos hX.1 ht.1).le, hXtpi.le⟩
    have hYt : Y * t ∈ Icc (0 : ℝ) Real.pi := by
      exact ⟨(mul_pos hY.1 ht.1).le, hYtpi.le⟩
    have hsinc := sinc_antitoneOn_Icc_zero_pi hXt hYt
      (mul_le_mul_of_nonneg_right hXY ht.1.le)
    have hsincX : 0 < Real.sinc (X * t) :=
      sinc_pos_of_mem_Ioo_zero_pi ⟨mul_pos hX.1 ht.1, hXtpi⟩
    have hsincY : 0 < Real.sinc (Y * t) :=
      sinc_pos_of_mem_Ioo_zero_pi ⟨mul_pos hY.1 ht.1, hYtpi⟩
    have hlog : Real.log (Real.sinc (Y * t)) ≤
        Real.log (Real.sinc (X * t)) :=
      Real.strictMonoOn_log.monotoneOn hsincY hsincX hsinc
    exact mul_le_mul_of_nonneg_left hlog (by linarith [ht.2])
  unfold circleCorrection
  linarith

lemma integral_log_sin_pi_mul :
    (∫ t : ℝ in 0..1, Real.log (Real.sin (Real.pi * t))) =
      -Real.log 2 := by
  rw [intervalIntegral.integral_comp_mul_left
    (f := fun x : ℝ ↦ Real.log (Real.sin x)) Real.pi_ne_zero]
  simp only [mul_zero, mul_one, integral_log_sin_zero_pi]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]

lemma intervalIntegrable_log_sin_pi_mul :
    IntervalIntegrable (fun t : ℝ ↦ Real.log (Real.sin (Real.pi * t)))
      volume 0 1 := by
  have h := (intervalIntegrable_log_sin
    (a := (0 : ℝ)) (b := Real.pi)).comp_mul_left (c := Real.pi)
  simpa [Function.comp_apply, Real.pi_ne_zero] using! h

lemma integral_one_sub_mul_log_sin_pi_mul :
    (∫ t : ℝ in 0..1,
      (1 - t) * Real.log (Real.sin (Real.pi * t))) =
        -Real.log 2 / 2 := by
  let L : ℝ → ℝ := fun t ↦ Real.log (Real.sin (Real.pi * t))
  have hL : IntervalIntegrable L volume 0 1 := by
    simpa [L] using! intervalIntegrable_log_sin_pi_mul
  have hleft : IntervalIntegrable (fun t ↦ (1 - t) * L t) volume 0 1 :=
    hL.continuousOn_mul (by fun_prop)
  have hright : IntervalIntegrable (fun t ↦ t * L t) volume 0 1 :=
    hL.continuousOn_mul (by fun_prop)
  have hsym :
      (∫ t : ℝ in 0..1, (1 - t) * L t) =
        ∫ t : ℝ in 0..1, t * L t := by
    calc
      (∫ t : ℝ in 0..1, (1 - t) * L t) =
          ∫ t : ℝ in 0..1, (fun u ↦ u * L u) (1 - t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp [L]
        have harg : Real.pi * (1 - t) = Real.pi - Real.pi * t := by ring
        rw [harg, Real.sin_pi_sub]
      _ = ∫ t : ℝ in (1 - 1)..(1 - 0), t * L t :=
        intervalIntegral.integral_comp_sub_left (fun u ↦ u * L u) 1
      _ = ∫ t : ℝ in 0..1, t * L t := by norm_num
  have hdecomp :
      (∫ t : ℝ in 0..1, L t) =
        (∫ t : ℝ in 0..1, (1 - t) * L t) +
          ∫ t : ℝ in 0..1, t * L t := by
    rw [← intervalIntegral.integral_add hleft hright]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have htotal : (∫ t : ℝ in 0..1, L t) = -Real.log 2 := by
    simpa [L] using! integral_log_sin_pi_mul
  linarith

lemma integral_one_sub_zero_one :
    (∫ t : ℝ in 0..1, 1 - t) = (1 / 2 : ℝ) := by
  calc
    (∫ t : ℝ in 0..1, 1 - t) =
        (∫ _t : ℝ in 0..1, 1) - ∫ t : ℝ in 0..1, t := by
      exact intervalIntegral.integral_sub intervalIntegrable_const
        (continuous_id.intervalIntegrable 0 1)
    _ = (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_const, integral_id]
      norm_num

lemma integral_circleCorrectionIntegrand_pi :
    (∫ t : ℝ in 0..1, circleCorrectionIntegrand Real.pi t) =
      -Real.log 2 / 2 - Real.log Real.pi / 2 + 3 / 4 := by
  have hsin : IntervalIntegrable
      (fun t : ℝ ↦ (1 - t) * Real.log (Real.sin (Real.pi * t)))
      volume 0 1 :=
    intervalIntegrable_log_sin_pi_mul.continuousOn_mul (by fun_prop)
  have hconst : IntervalIntegrable
      (fun t : ℝ ↦ Real.log Real.pi * (1 - t)) volume 0 1 := by
    exact (by fun_prop : Continuous
      (fun t : ℝ ↦ Real.log Real.pi * (1 - t))).intervalIntegrable 0 1
  have hlog : IntervalIntegrable
      (fun t : ℝ ↦ (1 - t) * Real.log t) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul (by fun_prop)
  calc
    (∫ t : ℝ in 0..1, circleCorrectionIntegrand Real.pi t) =
        ∫ t : ℝ in 0..1,
          (1 - t) * (Real.log (Real.sin (Real.pi * t)) -
            Real.log Real.pi - Real.log t) := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      filter_upwards [
        (log_sinc_mul_eventuallyEq Real.pi_pos).filter_mono
          (codiscreteWithin_uIoc_le_codiscrete 0 1)] with t ht
      dsimp [circleCorrectionIntegrand]
      rw [← ht]
    _ = (∫ t : ℝ in 0..1,
          (1 - t) * Real.log (Real.sin (Real.pi * t))) -
        Real.log Real.pi * (∫ t : ℝ in 0..1, 1 - t) -
          ∫ t : ℝ in 0..1, (1 - t) * Real.log t := by
      rw [show (fun t : ℝ ↦
          (1 - t) * (Real.log (Real.sin (Real.pi * t)) -
            Real.log Real.pi - Real.log t)) =
          fun t ↦ (1 - t) * Real.log (Real.sin (Real.pi * t)) -
            Real.log Real.pi * (1 - t) - (1 - t) * Real.log t by
          funext t
          ring]
      rw [intervalIntegral.integral_sub (hsin.sub hconst) hlog,
        intervalIntegral.integral_sub hsin hconst,
        intervalIntegral.integral_const_mul]
    _ = -Real.log 2 / 2 - Real.log Real.pi / 2 + 3 / 4 := by
      rw [integral_one_sub_mul_log_sin_pi_mul,
        integral_one_sub_zero_one, integral_one_sub_mul_log_zero_one]
      ring

theorem circleCorrection_pi :
    circleCorrection Real.pi = 0 := by
  unfold circleCorrection
  rw [integral_circleCorrectionIntegrand_pi,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

theorem circleCorrection_nonneg {X : ℝ} (hX : 0 < X)
    (hXpi : X ≤ Real.pi) :
    0 ≤ circleCorrection X := by
  have hmono := circleCorrection_antitoneOn
    (show X ∈ Ioc (0 : ℝ) Real.pi from ⟨hX, hXpi⟩)
    (show Real.pi ∈ Ioc (0 : ℝ) Real.pi from ⟨Real.pi_pos, le_rfl⟩)
    hXpi
  rwa [circleCorrection_pi] at hmono

lemma intervalIntegrable_one_sub_mul_log_sin_mul {X : ℝ} (hX : 0 < X) :
    IntervalIntegrable
      (fun t : ℝ ↦ (1 - t) * Real.log (Real.sin (X * t)))
      volume 0 1 := by
  have hsin := (intervalIntegrable_log_sin
    (a := (0 : ℝ)) (b := X)).comp_mul_left (c := X)
  have hsin' : IntervalIntegrable
      (fun t : ℝ ↦ Real.log (Real.sin (X * t))) volume 0 1 := by
    simpa [Function.comp_apply, hX.ne'] using! hsin
  exact hsin'.continuousOn_mul (by fun_prop)

lemma integral_circleCorrectionIntegrand_eq {X : ℝ} (hX : 0 < X) :
    (∫ t : ℝ in 0..1, circleCorrectionIntegrand X t) =
      (∫ t : ℝ in 0..1,
        (1 - t) * Real.log (Real.sin (X * t))) -
        Real.log X / 2 + 3 / 4 := by
  have hsin := intervalIntegrable_one_sub_mul_log_sin_mul hX
  have hconst : IntervalIntegrable
      (fun t : ℝ ↦ Real.log X * (1 - t)) volume 0 1 := by
    exact (by fun_prop : Continuous
      (fun t : ℝ ↦ Real.log X * (1 - t))).intervalIntegrable 0 1
  have hlog : IntervalIntegrable
      (fun t : ℝ ↦ (1 - t) * Real.log t) volume 0 1 :=
    intervalIntegral.intervalIntegrable_log'.continuousOn_mul (by fun_prop)
  calc
    (∫ t : ℝ in 0..1, circleCorrectionIntegrand X t) =
        ∫ t : ℝ in 0..1,
          (1 - t) * (Real.log (Real.sin (X * t)) -
            Real.log X - Real.log t) := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      filter_upwards [
        (log_sinc_mul_eventuallyEq hX).filter_mono
          (codiscreteWithin_uIoc_le_codiscrete 0 1)] with t ht
      dsimp [circleCorrectionIntegrand]
      rw [← ht]
    _ = (∫ t : ℝ in 0..1,
          (1 - t) * Real.log (Real.sin (X * t))) -
        Real.log X * (∫ t : ℝ in 0..1, 1 - t) -
          ∫ t : ℝ in 0..1, (1 - t) * Real.log t := by
      rw [show (fun t : ℝ ↦
          (1 - t) * (Real.log (Real.sin (X * t)) -
            Real.log X - Real.log t)) =
          fun t ↦ (1 - t) * Real.log (Real.sin (X * t)) -
            Real.log X * (1 - t) - (1 - t) * Real.log t by
          funext t
          ring]
      rw [intervalIntegral.integral_sub (hsin.sub hconst) hlog,
        intervalIntegral.integral_sub hsin hconst,
        intervalIntegral.integral_const_mul]
    _ = (∫ t : ℝ in 0..1,
          (1 - t) * Real.log (Real.sin (X * t))) -
        Real.log X / 2 + 3 / 4 := by
      rw [integral_one_sub_zero_one, integral_one_sub_mul_log_zero_one]
      ring

def circleSelfEnergyIntegrand (X t : ℝ) : ℝ :=
  (1 - t) * Real.log (2 * Real.sin (X * t))

def circleSelfEnergy (X : ℝ) : ℝ :=
  2 * ∫ t : ℝ in 0..1, circleSelfEnergyIntegrand X t

lemma sin_mul_ne_zero_mem_codiscrete {X : ℝ} (hX : 0 < X) :
    (fun t : ℝ ↦ Real.sin (X * t)) ⁻¹' {0}ᶜ ∈ codiscrete ℝ := by
  have hana : AnalyticOnNhd ℝ (fun t : ℝ ↦ Real.sin (X * t)) univ :=
    fun _ _ ↦ by fun_prop
  apply hana.preimage_zero_mem_codiscrete
    (x := (Real.pi / 2) / X)
  have harg : X * ((Real.pi / 2) / X) = Real.pi / 2 := by
    field_simp [hX.ne']
  rw [harg]
  simp

lemma integral_circleSelfEnergyIntegrand_eq {X : ℝ} (hX : 0 < X) :
    (∫ t : ℝ in 0..1, circleSelfEnergyIntegrand X t) =
      Real.log 2 / 2 +
        ∫ t : ℝ in 0..1,
          (1 - t) * Real.log (Real.sin (X * t)) := by
  have hsin := intervalIntegrable_one_sub_mul_log_sin_mul hX
  have hconst : IntervalIntegrable
      (fun t : ℝ ↦ Real.log 2 * (1 - t)) volume 0 1 := by
    exact (by fun_prop : Continuous
      (fun t : ℝ ↦ Real.log 2 * (1 - t))).intervalIntegrable 0 1
  have hsinzero :
      (fun t : ℝ ↦ Real.sin (X * t)) ⁻¹' {0}ᶜ ∈
        codiscreteWithin (Ι (0 : ℝ) 1) :=
    (codiscreteWithin_uIoc_le_codiscrete 0 1)
      (sin_mul_ne_zero_mem_codiscrete hX)
  calc
    (∫ t : ℝ in 0..1, circleSelfEnergyIntegrand X t) =
        ∫ t : ℝ in 0..1,
          Real.log 2 * (1 - t) +
            (1 - t) * Real.log (Real.sin (X * t)) := by
      apply intervalIntegral.integral_congr_codiscreteWithin
      filter_upwards [hsinzero] with t ht
      dsimp [circleSelfEnergyIntegrand]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ht]
      ring
    _ = Real.log 2 * (∫ t : ℝ in 0..1, 1 - t) +
        ∫ t : ℝ in 0..1,
          (1 - t) * Real.log (Real.sin (X * t)) := by
      rw [intervalIntegral.integral_add hconst hsin,
        intervalIntegral.integral_const_mul]
    _ = Real.log 2 / 2 +
        ∫ t : ℝ in 0..1,
          (1 - t) * Real.log (Real.sin (X * t)) := by
      rw [integral_one_sub_zero_one]
      ring

theorem circleSelfEnergy_eq_log_div_add_circleCorrection {X : ℝ}
    (hX : 0 < X) :
    circleSelfEnergy X = Real.log (X / Real.pi) + circleCorrection X := by
  unfold circleSelfEnergy circleCorrection
  rw [integral_circleSelfEnergyIntegrand_eq hX,
    integral_circleCorrectionIntegrand_eq hX,
    Real.log_div hX.ne' Real.pi_ne_zero,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero]
  ring

theorem log_div_pi_le_circleSelfEnergy {X : ℝ}
    (hX : 0 < X) (hXpi : X ≤ Real.pi) :
    Real.log (X / Real.pi) ≤ circleSelfEnergy X := by
  rw [circleSelfEnergy_eq_log_div_add_circleCorrection hX]
  exact le_add_of_nonneg_right (circleCorrection_nonneg hX hXpi)

end

end Erdos1038
