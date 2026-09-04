/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.HallOuter
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Measurability of Hall's radial logarithmic supremum

This file replaces the a priori uncountable supremum over radii in Hall's local logarithmic
kernel by a supremum over projected rational radii.  Lower semicontinuity of the kernel and
density of the projected rationals show that the two suprema agree.  Consequently the radial
supremum, and its Riesz-measure integral, are measurable.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology BigOperators

namespace Erdos515

lemma measurable_localLogKernel_uncurry :
    Measurable (Function.uncurry localLogKernel) := by
  unfold localLogKernel Function.uncurry
  apply Measurable.ite
  · exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
  · exact measurable_const
  · fun_prop

lemma tendsto_localLogKernel_self (ζ : ℂ) :
    Tendsto (localLogKernel ζ) (𝓝 ζ) (𝓝 ⊤) := by
  apply ENNReal.tendsto_nhds_top
  intro n
  filter_upwards [Metric.ball_mem_nhds ζ
      (div_pos (by norm_num : (0 : ℝ) < 4) (Real.exp_pos (n : ℝ)))]
    with z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  by_cases h : z = ζ
  · simp [localLogKernel, h]
  · rw [localLogKernel, if_neg h, ENNReal.natCast_lt_ofReal]
    apply (Real.lt_log_iff_exp_lt (div_pos (by norm_num : (0 : ℝ) < 4)
      (norm_pos_iff.mpr (sub_ne_zero.mpr h)))).2
    apply (lt_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr h))).2
    have := (lt_div_iff₀ (Real.exp_pos (n : ℝ))).1 hz
    simpa [mul_comm] using this

lemma continuousAt_localLogKernel (ζ z : ℂ) :
    ContinuousAt (localLogKernel ζ) z := by
  by_cases h : z = ζ
  · subst z
    simpa [ContinuousAt, localLogKernel] using tendsto_localLogKernel_self ζ
  · have hne : ∀ᶠ w in 𝓝 z, w ≠ ζ :=
      (isOpen_ne.mem_nhds h)
    apply ContinuousAt.congr_of_eventuallyEq
      (ENNReal.continuous_ofReal.continuousAt.comp
        (ContinuousAt.log
          (continuousAt_const.div
            (ContinuousAt.norm (continuousAt_id.sub continuousAt_const))
            (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)))
          (div_ne_zero (by norm_num : (4 : ℝ) ≠ 0)
            (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)))))
    filter_upwards [hne] with w hw
    simp [localLogKernel, hw]

lemma continuous_localLogKernel (ζ : ℂ) : Continuous (localLogKernel ζ) :=
  continuous_iff_continuousAt.2 (continuousAt_localLogKernel ζ)

lemma continuous_radialPoint_uncurry :
    Continuous (Function.uncurry radialPoint) := by
  unfold radialPoint Function.uncurry
  fun_prop

/-- Projection of a rational number to the compact interval of Hall radii. -/
noncomputable def rationalInnerRadius (q : ℚ) : innerRadii :=
  Set.projIcc 0 (1 / 2) (by norm_num) (q : ℝ)

lemma denseRange_rationalInnerRadius : DenseRange rationalInnerRadius := by
  change DenseRange
    (Set.projIcc 0 (1 / 2) (by norm_num) ∘ ((↑) : ℚ → ℝ))
  exact (Set.projIcc_surjective (by norm_num)).denseRange.comp
    Rat.denseRange_cast continuous_projIcc

/-- Countable version of Hall's radial logarithmic supremum. -/
noncomputable def rationalRadialLogKernel (ζ : ℂ) (θ : ℝ) : ℝ≥0∞ :=
  ⨆ q : ℚ, localLogKernel ζ (radialPoint (rationalInnerRadius q).1 θ)

lemma rationalRadialLogKernel_eq (ζ : ℂ) (θ : ℝ) :
    rationalRadialLogKernel ζ θ = radialLogKernel ζ θ := by
  apply le_antisymm
  · refine iSup_le fun q ↦ ?_
    exact le_iSup (fun r : innerRadii ↦
      localLogKernel ζ (radialPoint r.1 θ)) (rationalInnerRadius q)
  · refine iSup_le fun r ↦ ?_
    apply DenseRange.induction_on denseRange_rationalInnerRadius
      (p := fun r : innerRadii ↦
        localLogKernel ζ (radialPoint r.1 θ) ≤ rationalRadialLogKernel ζ θ) r
    · apply isClosed_le
      · exact (continuous_localLogKernel ζ).comp
          (continuous_radialPoint_uncurry.comp
            (continuous_subtype_val.prodMk continuous_const))
      · exact continuous_const
    · intro q
      exact le_iSup (fun q : ℚ ↦
        localLogKernel ζ (radialPoint (rationalInnerRadius q).1 θ)) q

lemma measurable_rationalRadialLogKernel_uncurry :
    Measurable (Function.uncurry rationalRadialLogKernel) := by
  unfold rationalRadialLogKernel Function.uncurry
  apply Measurable.iSup
  intro q
  have hpoint : Measurable (fun b : ℂ × ℝ ↦
      (b.1, radialPoint (rationalInnerRadius q).1 b.2)) :=
    measurable_fst.prodMk
      (continuous_radialPoint_uncurry.measurable.comp
        (measurable_const.prodMk measurable_snd))
  simpa [Function.comp_def] using measurable_localLogKernel_uncurry.comp hpoint

lemma measurable_radialLogKernel_uncurry :
    Measurable (Function.uncurry radialLogKernel) := by
  convert measurable_rationalRadialLogKernel_uncurry using 1
  ext p
  exact (rationalRadialLogKernel_eq p.1 p.2).symm

lemma measurable_innerRieszMajorant (μ : Measure ℂ) [SFinite μ] :
    Measurable (innerRieszMajorant μ) := by
  exact measurable_radialLogKernel_uncurry.lintegral_prod_left

/-! ### The concrete one-kernel estimate (17) -/

/-- Every point of a radial segment has distance at least the transverse component of `ζ`.
This is the elementary geometric input in Hall's one-kernel estimate. -/
lemma norm_radialPoint_sub_ge_mul_abs_sin (ζ : ℂ) (r θ : ℝ) :
    ‖ζ‖ * |Real.sin (θ - ζ.arg)| ≤ ‖radialPoint r θ - ζ‖ := by
  have hrotζ : Complex.exp ((-θ : ℂ) * Complex.I) * ζ =
      (‖ζ‖ : ℂ) * Complex.exp (((ζ.arg - θ : ℝ) : ℂ) * Complex.I) := by
    conv_lhs => rhs; rw [← Complex.norm_mul_exp_arg_mul_I ζ]
    calc
      Complex.exp ((-θ : ℂ) * Complex.I) *
          ((‖ζ‖ : ℂ) * Complex.exp ((ζ.arg : ℂ) * Complex.I)) =
          (‖ζ‖ : ℂ) * (Complex.exp ((-θ : ℂ) * Complex.I) *
            Complex.exp ((ζ.arg : ℂ) * Complex.I)) := by ring
      _ = (‖ζ‖ : ℂ) * Complex.exp
          (((-θ : ℂ) * Complex.I) + ((ζ.arg : ℂ) * Complex.I)) := by
            rw [Complex.exp_add]
      _ = _ := by
        congr 2
        push_cast
        ring
  have hrotr : Complex.exp ((-θ : ℂ) * Complex.I) * radialPoint r θ = (r : ℂ) := by
    calc
      Complex.exp ((-θ : ℂ) * Complex.I) * radialPoint r θ =
          (r : ℂ) * (Complex.exp ((-θ : ℂ) * Complex.I) *
            Complex.exp ((θ : ℂ) * Complex.I)) := by simp [radialPoint]; ring
      _ = (r : ℂ) * Complex.exp
          (((-θ : ℂ) * Complex.I) + ((θ : ℂ) * Complex.I)) := by rw [Complex.exp_add]
      _ = (r : ℂ) := by ring_nf; simp
  have him : ((‖ζ‖ : ℂ) * Complex.exp (((ζ.arg - θ : ℝ) : ℂ) * Complex.I)).im =
      ‖ζ‖ * Real.sin (ζ.arg - θ) := by
    simpa [circleMap] using circleMap_zero_im ‖ζ‖ (ζ.arg - θ)
  calc
    ‖ζ‖ * |Real.sin (θ - ζ.arg)| =
        |(Complex.exp ((-θ : ℂ) * Complex.I) * (radialPoint r θ - ζ)).im| := by
      rw [mul_sub, hrotr, hrotζ]
      rw [Complex.sub_im, Complex.ofReal_im, him]
      rw [zero_sub, abs_neg, abs_mul, abs_of_nonneg (norm_nonneg ζ)]
      congr 1
      rw [show ζ.arg - θ = -(θ - ζ.arg) by ring, Real.sin_neg, abs_neg]
    _ ≤ ‖Complex.exp ((-θ : ℂ) * Complex.I) * (radialPoint r θ - ζ)‖ :=
      Complex.abs_im_le_norm _
    _ = ‖radialPoint r θ - ζ‖ := by
      rw [norm_mul]
      have he : ‖Complex.exp ((-θ : ℂ) * Complex.I)‖ = 1 := by
        simp [Complex.norm_exp]
      rw [he]
      simp

/-- The logarithm of the absolute value of sine.  Lean's real logarithm satisfies
`log |x| = log x`, including at zero, which makes this a convenient integrable representative. -/
noncomputable def hallLogAbsSin (x : ℝ) : ℝ := Real.log |Real.sin x|

lemma intervalIntegrable_hallLogAbsSin (a b : ℝ) :
    IntervalIntegrable hallLogAbsSin volume a b := by
  have hfun : hallLogAbsSin = Real.log ∘ Real.sin := by
    funext x
    exact Real.log_abs x.sin
  rw [hfun]
  exact intervalIntegrable_log_sin

lemma periodic_hallLogAbsSin : Function.Periodic hallLogAbsSin Real.pi := by
  intro x
  simp [hallLogAbsSin, Real.sin_add]

lemma integral_hallLogAbsSin_zero_pi :
    ∫ x in (0 : ℝ)..Real.pi, hallLogAbsSin x = -Real.log 2 * Real.pi := by
  rw [← integral_log_sin_zero_pi]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) Real.pi := by
    simpa [Real.pi_pos.le] using hx
  rw [hallLogAbsSin, abs_of_nonneg]
  exact Real.sin_nonneg_of_nonneg_of_le_pi hx'.1 hx'.2

lemma integral_hallLogAbsSin_shift_zero_two_pi (φ : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), hallLogAbsSin (θ - φ) =
      -2 * Real.log 2 * Real.pi := by
  have hfirst : ∫ θ in (0 : ℝ)..Real.pi, hallLogAbsSin (θ - φ) =
      -Real.log 2 * Real.pi := by
    rw [intervalIntegral.integral_comp_sub_right]
    calc
      (∫ x in (0 : ℝ) - φ..Real.pi - φ, hallLogAbsSin x) =
          ∫ x in (0 : ℝ)..Real.pi, hallLogAbsSin x := by
        convert periodic_hallLogAbsSin.intervalIntegral_add_eq ((0 : ℝ) - φ) 0 using 1 <;>
          ring_nf
      _ = _ := integral_hallLogAbsSin_zero_pi
  have hshiftPeriodic : Function.Periodic (fun θ ↦ hallLogAbsSin (θ - φ)) Real.pi :=
    fun θ ↦ by
      convert periodic_hallLogAbsSin (θ - φ) using 1 <;> ring_nf
  have hint1 : IntervalIntegrable (fun θ ↦ hallLogAbsSin (θ - φ)) volume 0 Real.pi := by
    convert (intervalIntegrable_hallLogAbsSin (-φ) (Real.pi - φ)).comp_sub_right φ using 1 <;>
      ring
  have hint2 : IntervalIntegrable (fun θ ↦ hallLogAbsSin (θ - φ)) volume Real.pi
      (2 * Real.pi) := by
    convert (intervalIntegrable_hallLogAbsSin (Real.pi - φ)
      (2 * Real.pi - φ)).comp_sub_right φ using 1 <;> ring
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  rw [hfirst]
  have hsecond : ∫ θ in Real.pi..(2 * Real.pi), hallLogAbsSin (θ - φ) =
      -Real.log 2 * Real.pi := by
    calc
      (∫ θ in Real.pi..(2 * Real.pi), hallLogAbsSin (θ - φ)) =
          ∫ θ in (0 : ℝ)..Real.pi, hallLogAbsSin (θ - φ) := by
        convert hshiftPeriodic.intervalIntegral_add_eq Real.pi 0 using 1 <;> ring_nf
      _ = _ := hfirst
  rw [hsecond]
  ring

lemma localLogKernel_radialPoint_le_log_sin {ζ : ℂ} (hζ : ζ ≠ 0) {r θ : ℝ}
    (hsin : Real.sin (θ - ζ.arg) ≠ 0) :
    localLogKernel ζ (radialPoint r θ) ≤ ENNReal.ofReal
      (Real.log (4 / ‖ζ‖) - hallLogAbsSin (θ - ζ.arg)) := by
  have hρ : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hs : 0 < |Real.sin (θ - ζ.arg)| := abs_pos.mpr hsin
  have hdist : 0 < ‖radialPoint r θ - ζ‖ :=
    lt_of_lt_of_le (mul_pos hρ hs) (norm_radialPoint_sub_ge_mul_abs_sin ζ r θ)
  have hne : radialPoint r θ ≠ ζ := sub_ne_zero.mp (norm_ne_zero_iff.mp hdist.ne')
  rw [localLogKernel, if_neg hne]
  apply ENNReal.ofReal_le_ofReal
  rw [show Real.log (4 / ‖ζ‖) - hallLogAbsSin (θ - ζ.arg) =
      Real.log (4 / (‖ζ‖ * |Real.sin (θ - ζ.arg)|)) by
    simp only [hallLogAbsSin]
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) hρ.ne',
      Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (mul_ne_zero hρ.ne' hs.ne'),
      Real.log_mul hρ.ne' hs.ne']
    ring]
  apply Real.strictMonoOn_log.monotoneOn
  · exact div_pos (by norm_num) hdist
  · exact div_pos (by norm_num) (mul_pos hρ hs)
  · exact div_le_div_of_nonneg_left (by norm_num) (mul_pos hρ hs)
      (norm_radialPoint_sub_ge_mul_abs_sin ζ r θ)

lemma radialLogKernel_le_log_sin {ζ : ℂ} (hζ : ζ ≠ 0) {θ : ℝ}
    (hsin : Real.sin (θ - ζ.arg) ≠ 0) :
    radialLogKernel ζ θ ≤ ENNReal.ofReal
      (Real.log (4 / ‖ζ‖) - hallLogAbsSin (θ - ζ.arg)) := by
  refine iSup_le fun r ↦ ?_
  exact localLogKernel_radialPoint_le_log_sin hζ hsin

lemma ae_sin_sub_ne_zero (φ : ℝ) (s : Set ℝ) :
    ∀ᵐ θ ∂volume.restrict s, Real.sin (θ - φ) ≠ 0 := by
  have hcount : {θ : ℝ | Real.sin (θ - φ) = 0}.Countable := by
    apply Set.Countable.mono (s₂ := Set.range (fun n : ℤ ↦ φ + n * Real.pi))
    · intro θ hθ
      rw [Set.mem_ofPred_eq, Real.sin_eq_zero_iff] at hθ
      obtain ⟨n, hn⟩ := hθ
      refine ⟨n, ?_⟩
      linarith
    · exact Set.countable_range _
  rw [ae_iff]
  simpa only [ne_eq, not_not] using hcount.measure_zero (volume.restrict s)

lemma lintegral_log_sin_majorant_eq {ζ : ℂ} (hζ : ζ ≠ 0) (hρ : ‖ζ‖ < 1 / 4) :
    ∫⁻ θ in angleDomain, ENNReal.ofReal
        (Real.log (4 / ‖ζ‖) - hallLogAbsSin (θ - ζ.arg)) =
      ENNReal.ofReal (2 * Real.pi *
        (Real.log (4 / ‖ζ‖) + Real.log 2)) := by
  let B : ℝ := Real.log (4 / ‖ζ‖)
  let g : ℝ → ℝ := fun θ ↦ B - hallLogAbsSin (θ - ζ.arg)
  have hρ0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hB : 0 < B := by
    dsimp [B]
    rw [Real.log_pos_iff (by positivity : 0 ≤ 4 / ‖ζ‖)]
    apply (lt_div_iff₀ hρ0).2
    nlinarith
  have hg0 : ∀ θ, 0 ≤ g θ := by
    intro θ
    have hs0 : 0 ≤ |Real.sin (θ - ζ.arg)| := abs_nonneg _
    have hs1 : |Real.sin (θ - ζ.arg)| ≤ 1 := Real.abs_sin_le_one _
    have hlog : hallLogAbsSin (θ - ζ.arg) ≤ 0 := Real.log_nonpos hs0 hs1
    dsimp [g]
    linarith
  have hshift : IntervalIntegrable (fun θ ↦ hallLogAbsSin (θ - ζ.arg)) volume 0
      (2 * Real.pi) := by
    convert (intervalIntegrable_hallLogAbsSin (-ζ.arg)
      (2 * Real.pi - ζ.arg)).comp_sub_right ζ.arg using 1 <;> ring
  have hgIntI : IntervalIntegrable g volume 0 (2 * Real.pi) :=
    intervalIntegrable_const.sub hshift
  have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hgInt : Integrable g (volume.restrict angleDomain) := by
    rw [angleDomain]
    exact (intervalIntegrable_iff_integrableOn_Ico_of_le hle).1 hgIntI
  have hreal : ∫ θ, g θ ∂volume.restrict angleDomain =
      2 * Real.pi * (B + Real.log 2) := by
    rw [angleDomain, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
    rw [show (∫ θ in (0 : ℝ)..(2 * Real.pi), g θ) =
        (∫ θ in (0 : ℝ)..(2 * Real.pi), B) -
          ∫ θ in (0 : ℝ)..(2 * Real.pi), hallLogAbsSin (θ - ζ.arg) by
      exact intervalIntegral.integral_sub intervalIntegrable_const hshift]
    rw [intervalIntegral.integral_const, integral_hallLogAbsSin_shift_zero_two_pi]
    ring
  change (∫⁻ θ, ENNReal.ofReal (g θ) ∂volume.restrict angleDomain) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hgInt (ae_of_all _ hg0), hreal]

lemma log_sin_majorant_le_ten_base {ζ : ℂ} (hζ : ζ ≠ 0) (hρ : ‖ζ‖ < 1 / 4) :
    ENNReal.ofReal (2 * Real.pi *
        (Real.log (4 / ‖ζ‖) + Real.log 2)) ≤
      10 * ENNReal.ofReal (Real.log (4 / ‖ζ‖)) := by
  have hρ0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  have hB : 0 < Real.log (4 / ‖ζ‖) := by
    rw [Real.log_pos_iff (by positivity : 0 ≤ 4 / ‖ζ‖)]
    apply (lt_div_iff₀ hρ0).2
    nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    calc
      Real.log 16 = Real.log ((2 : ℝ) ^ 4) := by norm_num
      _ = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hratio : 16 < 4 / ‖ζ‖ := by
    apply (lt_div_iff₀ hρ0).2
    nlinarith
  have hlogratio : 4 * Real.log 2 ≤ Real.log (4 / ‖ζ‖) := by
    rw [← hlog16]
    exact Real.strictMonoOn_log.monotoneOn (by norm_num)
      (div_pos (by norm_num) hρ0) (le_of_lt hratio)
  calc
    ENNReal.ofReal (2 * Real.pi *
        (Real.log (4 / ‖ζ‖) + Real.log 2)) ≤
        ENNReal.ofReal (10 * Real.log (4 / ‖ζ‖)) := by
      apply ENNReal.ofReal_le_ofReal
      have hpi : Real.pi < 4 := Real.pi_lt_four
      nlinarith
    _ = 10 * ENNReal.ofReal (Real.log (4 / ‖ζ‖)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num

/-- Hall's concrete one-kernel estimate (17).  The explicit universal constant `10` is more
than sufficient; the proof integrates the exact logarithmic sine singularity. -/
theorem logKernel_radialMax_integral {ζ : ℂ} (hζ : ζ ∈ innerDisk) :
    ∫⁻ θ in angleDomain, radialLogKernel ζ θ ≤
      10 * localLogKernel ζ 0 := by
  have hρ : ‖ζ‖ < 1 / 4 := by
    simpa [innerDisk, Metric.mem_ball, dist_eq_norm] using hζ
  by_cases hζ0 : ζ = 0
  · subst ζ
    simp [localLogKernel]
  · calc
      (∫⁻ θ in angleDomain, radialLogKernel ζ θ) ≤
          ∫⁻ θ in angleDomain, ENNReal.ofReal
            (Real.log (4 / ‖ζ‖) - hallLogAbsSin (θ - ζ.arg)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_sin_sub_ne_zero ζ.arg angleDomain] with θ hθ
        exact radialLogKernel_le_log_sin hζ0 hθ
      _ = ENNReal.ofReal (2 * Real.pi *
          (Real.log (4 / ‖ζ‖) + Real.log 2)) :=
        lintegral_log_sin_majorant_eq hζ0 hρ
      _ ≤ 10 * ENNReal.ofReal (Real.log (4 / ‖ζ‖)) :=
        log_sin_majorant_le_ten_base hζ0 hρ
      _ = 10 * localLogKernel ζ 0 := by
        simp [localLogKernel, Ne.symm hζ0]

/-- The inner projection estimate with both former measurability arguments discharged. -/
theorem hall_inner_projection_measurable {μ : Measure ℂ} [SFinite μ] {S : Set ℝ}
    {ε C K δ : ℝ≥0∞}
    (hSmeas : MeasurableSet S) (hS : S ⊆ angleDomain)
    (hkernel : ∀ ζ ∈ innerDisk,
      ∫⁻ θ in angleDomain, radialLogKernel ζ θ ≤ C * localLogKernel ζ 0)
    (hlarge : S ⊆ {θ | ε ≤ innerRieszMajorant μ θ})
    (hε0 : ε ≠ 0) (hεtop : ε ≠ ⊤)
    (hmass : innerRieszMass μ ≤ K * δ) :
    volume S ≤ (C * (K * δ)) / ε := by
  apply hall_inner_projection hSmeas hS
    measurable_radialLogKernel_uncurry.aemeasurable hkernel
    (measurable_innerRieszMajorant μ).aemeasurable hlarge hε0 hεtop hmass

/-! ### Direct normalized Green-kernel estimate on inner circles

The following estimate is the analytic input for a direct slit-potential proof of the inner
part of Hall's lemma.  It avoids introducing a Riesz measure.  The zero set of the shifted sine
is null, and the common majorant has integral exactly `5 * π` on the angle domain. -/

noncomputable def normalizedInnerGreenMajorant (z : ℂ) (θ : ℝ) : ℝ :=
  2 + (-hallLogAbsSin (θ - z.arg)) / Real.log 4

lemma hallLogAbsSin_nonpos (x : ℝ) : hallLogAbsSin x ≤ 0 := by
  exact Real.log_nonpos (abs_nonneg _) (Real.abs_sin_le_one _)

lemma normalizedInnerGreenMajorant_two_le (z : ℂ) (θ : ℝ) :
    2 ≤ normalizedInnerGreenMajorant z θ := by
  unfold normalizedInnerGreenMajorant
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hnonneg : 0 ≤ -hallLogAbsSin (θ - z.arg) := by
    exact neg_nonneg.mpr (hallLogAbsSin_nonpos _)
  exact le_add_of_nonneg_right (div_nonneg hnonneg hlog4.le)

/-- For a pole on a circle of radius at most `1 / 4`, the Green kernel normalized by its
value at the origin is bounded, off the null radial alignment set, by a single integrable
function independent of the radius. -/
lemma diskGreen_div_log_le_normalizedInnerGreenMajorant
    {z : ℂ} (hz : ‖z‖ < 1) {r θ : ℝ}
    (hr : 0 < r) (hrq : r ≤ 1 / 4)
    (hsin : Real.sin (θ - z.arg) ≠ 0) :
    diskGreen z (radialPoint r θ) / Real.log (1 / r) ≤
      normalizedInnerGreenMajorant z θ := by
  let ζ := radialPoint r θ
  let ρ := ‖z‖
  let L := Real.log (1 / r)
  have hr1 : r < 1 := lt_of_le_of_lt hrq (by norm_num)
  have hζnorm : ‖ζ‖ = r := by simp [ζ, radialPoint, abs_of_pos hr]
  have hζdisk : ‖ζ‖ < 1 := hζnorm.trans_lt hr1
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (one_lt_one_div hr hr1)
  have hL4 : Real.log 4 ≤ L := by
    apply Real.strictMonoOn_log.monotoneOn
    · norm_num
    · exact div_pos (by norm_num) hr
    · rw [le_div_iff₀ hr]
      nlinarith
  have hN : ‖1 - (starRingEnd ℂ) ζ * z‖ ≤ 5 / 4 := by
    calc
      ‖1 - (starRingEnd ℂ) ζ * z‖ ≤
          ‖(1 : ℂ)‖ + ‖(starRingEnd ℂ) ζ * z‖ := norm_sub_le _ _
      _ = 1 + r * ρ := by simp [hζnorm, ρ, Complex.norm_conj]
      _ ≤ 5 / 4 := by
        have hρ0 : 0 ≤ ρ := norm_nonneg z
        have hρ1 : ρ ≤ 1 := hz.le
        nlinarith [mul_le_mul hrq hρ1 hρ0 (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hnumpos : 0 < ‖1 - (starRingEnd ℂ) ζ * z‖ := by
    by_contra hn
    have hn0 : ‖1 - (starRingEnd ℂ) ζ * z‖ = 0 :=
      le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    have hzero : 1 - (starRingEnd ℂ) ζ * z = 0 := norm_eq_zero.mp hn0
    have hp : ‖ζ‖ * ‖z‖ = 1 := by
      have heq : (starRingEnd ℂ) ζ * z = 1 := (sub_eq_zero.mp hzero).symm
      have := congrArg norm heq
      simpa [norm_mul, Complex.norm_conj] using this
    have : ‖ζ‖ * ‖z‖ < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg ζ) hζdisk hz.le
    linarith
  have hlog_nonneg : 0 ≤ -hallLogAbsSin (θ - z.arg) :=
    neg_nonneg.mpr (hallLogAbsSin_nonpos _)
  have hH2 := normalizedInnerGreenMajorant_two_le z θ
  by_cases hlow : r ≤ ρ / 2
  · have hdist : r ≤ ‖z - ζ‖ := by
      have hrev : ρ - r ≤ ‖z - ζ‖ := by
        have ht := norm_sub_norm_le z ζ
        rw [hζnorm] at ht
        simpa [ρ] using ht
      nlinarith
    have hdistpos : 0 < ‖z - ζ‖ := lt_of_lt_of_le hr hdist
    have hratio : ‖1 - (starRingEnd ℂ) ζ * z‖ / ‖z - ζ‖ ≤ 1 / r ^ 2 := by
      calc
        _ ≤ (5 / 4) / r := div_le_div₀ (by norm_num) hN hr hdist
        _ ≤ 1 / r ^ 2 := by
          rw [div_le_div_iff₀ hr (sq_pos_of_pos hr)]
          nlinarith
    have hlog : diskGreen z ζ ≤ 2 * L := by
      rw [diskGreen]
      calc
        Real.log (‖1 - (starRingEnd ℂ) ζ * z‖ / ‖z - ζ‖) ≤
            Real.log (1 / r ^ 2) := by
          exact Real.strictMonoOn_log.monotoneOn (div_pos hnumpos hdistpos)
            (show 0 < (1 / r ^ 2 : ℝ) by positivity) hratio
        _ = 2 * L := by
          dsimp [L]
          rw [show 1 / r ^ 2 = (1 / r) ^ 2 by field_simp, Real.log_pow]
          norm_num
    exact (div_le_iff₀ hL).2 hlog |>.trans hH2
  · by_cases hhigh : 2 * ρ ≤ r
    · have hdist : r / 2 ≤ ‖z - ζ‖ := by
        have hrev : r - ρ ≤ ‖z - ζ‖ := by
          have ht := norm_sub_norm_le ζ z
          rw [hζnorm] at ht
          simpa [ρ, norm_sub_rev] using ht
        nlinarith
      have hdistpos : 0 < ‖z - ζ‖ := lt_of_lt_of_le (half_pos hr) hdist
      have hratio : ‖1 - (starRingEnd ℂ) ζ * z‖ / ‖z - ζ‖ ≤ 1 / r ^ 2 := by
        calc
          _ ≤ (5 / 4) / (r / 2) :=
            div_le_div₀ (by norm_num) hN (half_pos hr) hdist
          _ ≤ 1 / r ^ 2 := by
            rw [div_le_div_iff₀ (half_pos hr) (sq_pos_of_pos hr)]
            nlinarith
      have hlog : diskGreen z ζ ≤ 2 * L := by
        rw [diskGreen]
        calc
          Real.log (‖1 - (starRingEnd ℂ) ζ * z‖ / ‖z - ζ‖) ≤
              Real.log (1 / r ^ 2) := by
            exact Real.strictMonoOn_log.monotoneOn (div_pos hnumpos hdistpos)
              (show 0 < (1 / r ^ 2 : ℝ) by positivity) hratio
          _ = 2 * L := by
            dsimp [L]
            rw [show 1 / r ^ 2 = (1 / r) ^ 2 by field_simp, Real.log_pow]
            norm_num
      exact (div_le_iff₀ hL).2 hlog |>.trans hH2
    · have hρlower : r / 2 < ρ := by linarith
      have hspos : 0 < |Real.sin (θ - z.arg)| := abs_pos.mpr hsin
      have hdist : (r / 2) * |Real.sin (θ - z.arg)| < ‖ζ - z‖ := by
        calc
          (r / 2) * |Real.sin (θ - z.arg)| <
              ρ * |Real.sin (θ - z.arg)| := mul_lt_mul_of_pos_right hρlower hspos
          _ ≤ ‖radialPoint r θ - z‖ := norm_radialPoint_sub_ge_mul_abs_sin z r θ
          _ = ‖ζ - z‖ := rfl
      have hdistpos : 0 < ‖z - ζ‖ := by
        have ht : 0 < ‖ζ - z‖ :=
          lt_of_lt_of_le (mul_pos (half_pos hr) hspos) hdist.le
        simpa [norm_sub_rev] using ht
      have hratio : ‖1 - (starRingEnd ℂ) ζ * z‖ / ‖z - ζ‖ ≤
          1 / (r ^ 2 * |Real.sin (θ - z.arg)|) := by
        have hD : (r / 2) * |Real.sin (θ - z.arg)| ≤ ‖z - ζ‖ := by
          simpa [norm_sub_rev] using hdist.le
        calc
          _ ≤ (5 / 4) / ((r / 2) * |Real.sin (θ - z.arg)|) :=
            div_le_div₀ (by norm_num) hN (mul_pos (half_pos hr) hspos) hD
          _ ≤ 1 / (r ^ 2 * |Real.sin (θ - z.arg)|) := by
            rw [div_le_div_iff₀ (mul_pos (half_pos hr) hspos)
              (mul_pos (sq_pos_of_pos hr) hspos)]
            calc
              (5 / 4 : ℝ) * (r ^ 2 * |Real.sin (θ - z.arg)|) =
                  ((5 / 4 : ℝ) * r ^ 2) * |Real.sin (θ - z.arg)| := by ring
              _ ≤ (r / 2) * |Real.sin (θ - z.arg)| := by
                apply mul_le_mul_of_nonneg_right _ hspos.le
                nlinarith
              _ = 1 * (r / 2 * |Real.sin (θ - z.arg)|) := by ring
      have hlog : diskGreen z ζ ≤ 2 * L - hallLogAbsSin (θ - z.arg) := by
        rw [diskGreen]
        calc
          Real.log (‖1 - (starRingEnd ℂ) ζ * z‖ / ‖z - ζ‖) ≤
              Real.log (1 / (r ^ 2 * |Real.sin (θ - z.arg)|)) := by
            exact Real.strictMonoOn_log.monotoneOn (div_pos hnumpos hdistpos)
              (show 0 < (1 / (r ^ 2 * |Real.sin (θ - z.arg)|) : ℝ) by positivity)
              hratio
          _ = 2 * L - hallLogAbsSin (θ - z.arg) := by
            dsimp [L, hallLogAbsSin]
            rw [Real.log_div (by norm_num)
                (mul_ne_zero (pow_ne_zero 2 hr.ne') hspos.ne'),
              Real.log_mul (pow_ne_zero 2 hr.ne') hspos.ne', Real.log_pow,
              Real.log_div (by norm_num) hr.ne']
            norm_num
            ring
      have hdiv : diskGreen z ζ / L ≤
          2 + (-hallLogAbsSin (θ - z.arg)) / L := by
        calc
          diskGreen z ζ / L ≤
              (2 * L - hallLogAbsSin (θ - z.arg)) / L :=
            div_le_div_of_nonneg_right hlog hL.le
          _ = 2 + (-hallLogAbsSin (θ - z.arg)) / L := by
            field_simp
            ring
      have hfrac : (-hallLogAbsSin (θ - z.arg)) / L ≤
          (-hallLogAbsSin (θ - z.arg)) / Real.log 4 := by
        exact div_le_div_of_nonneg_left hlog_nonneg (Real.log_pos (by norm_num)) hL4
      exact hdiv.trans (by unfold normalizedInnerGreenMajorant; linarith)

/-- Extended-real form of `diskGreen_div_log_le_normalizedInnerGreenMajorant`.  The hypothesis
excluding a shifted sine zero also excludes the genuine Green pole. -/
lemma diskGreenENNReal_div_log_le_normalizedInnerGreenMajorant
    {z : ℂ} (hz : ‖z‖ < 1) {r θ : ℝ}
    (hr : 0 < r) (hrq : r ≤ 1 / 4)
    (hsin : Real.sin (θ - z.arg) ≠ 0) :
    diskGreenENNReal z (radialPoint r θ) /
        ENNReal.ofReal (Real.log (1 / r)) ≤
      ENNReal.ofReal (normalizedInnerGreenMajorant z θ) := by
  have hr1 : r < 1 := lt_of_le_of_lt hrq (by norm_num)
  have hL : 0 < Real.log (1 / r) := Real.log_pos (one_lt_one_div hr hr1)
  have hne : z ≠ radialPoint r θ := by
    intro heq
    have htrans := norm_radialPoint_sub_ge_mul_abs_sin z r θ
    rw [heq] at htrans
    simp [radialPoint, abs_of_pos hr] at htrans
    have hs0 : |Real.sin (θ - (radialPoint r θ).arg)| = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right htrans hr) (abs_nonneg _)
    apply hsin
    rw [heq]
    exact abs_eq_zero.mp hs0
  rw [diskGreenENNReal_of_ne hne, ← ENNReal.ofReal_div_of_pos hL]
  exact ENNReal.ofReal_le_ofReal
    (diskGreen_div_log_le_normalizedInnerGreenMajorant hz hr hrq hsin)

/-- The common normalized inner Green-kernel majorant has exact integral `5 * π`. -/
lemma lintegral_normalizedInnerGreenMajorant (z : ℂ) :
    ∫⁻ θ in angleDomain, ENNReal.ofReal (normalizedInnerGreenMajorant z θ) =
      ENNReal.ofReal (5 * Real.pi) := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hshift : IntervalIntegrable
      (fun θ ↦ hallLogAbsSin (θ - z.arg)) volume 0 (2 * Real.pi) := by
    convert (intervalIntegrable_hallLogAbsSin (-z.arg)
      (2 * Real.pi - z.arg)).comp_sub_right z.arg using 1 <;> ring
  have hmajorI : IntervalIntegrable (normalizedInnerGreenMajorant z)
      volume 0 (2 * Real.pi) := by
    have hneg : IntervalIntegrable
        (fun θ ↦ -hallLogAbsSin (θ - z.arg)) volume 0 (2 * Real.pi) := hshift.neg
    have hdiv : IntervalIntegrable
        (fun θ ↦ (-hallLogAbsSin (θ - z.arg)) / Real.log 4)
        volume 0 (2 * Real.pi) := hneg.div_const _
    have hconst : IntervalIntegrable (fun _θ : ℝ ↦ (2 : ℝ))
        volume 0 (2 * Real.pi) := intervalIntegrable_const
    convert hconst.add hdiv using 1
    ext x
    rfl
  have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hmajor : Integrable (normalizedInnerGreenMajorant z)
      (volume.restrict angleDomain) := by
    rw [angleDomain]
    exact (intervalIntegrable_iff_integrableOn_Ico_of_le hle).1 hmajorI
  have hnonneg : ∀ θ, 0 ≤ normalizedInnerGreenMajorant z θ := fun θ ↦
    (normalizedInnerGreenMajorant_two_le z θ).trans' (by norm_num)
  have hreal : ∫ θ, normalizedInnerGreenMajorant z θ
      ∂volume.restrict angleDomain = 5 * Real.pi := by
    rw [angleDomain, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle]
    have hneg : IntervalIntegrable
        (fun θ ↦ -hallLogAbsSin (θ - z.arg)) volume 0 (2 * Real.pi) := hshift.neg
    have hdiv : IntervalIntegrable
        (fun θ ↦ (-hallLogAbsSin (θ - z.arg)) / Real.log 4)
        volume 0 (2 * Real.pi) := hneg.div_const _
    rw [show (∫ θ in (0 : ℝ)..(2 * Real.pi), normalizedInnerGreenMajorant z θ) =
        (∫ _θ in (0 : ℝ)..(2 * Real.pi), (2 : ℝ)) +
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (-hallLogAbsSin (θ - z.arg)) / Real.log 4 by
      apply intervalIntegral.integral_add intervalIntegrable_const hdiv]
    have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
      calc
        Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
        _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [intervalIntegral.integral_const,
      intervalIntegral.integral_div,
      intervalIntegral.integral_neg,
      integral_hallLogAbsSin_shift_zero_two_pi,
      hlog4eq]
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
    field_simp
    ring
  change (∫⁻ θ, ENNReal.ofReal (normalizedInnerGreenMajorant z θ)
    ∂volume.restrict angleDomain) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hmajor (ae_of_all _ hnonneg), hreal]

lemma measurable_diskGreenENNReal_right (z : ℂ) :
    Measurable (fun ζ : ℂ ↦ diskGreenENNReal z ζ) := by
  unfold diskGreenENNReal diskGreen
  apply Measurable.ite
  · exact measurableSet_eq_fun measurable_const measurable_id
  · exact measurable_const
  · fun_prop

/-- One inner logarithmically normalized slit is controlled by the common angular majorant. -/
lemma greenPotential_logWeightedMeasure_le_inner (a : CircularArc) {z : ℂ}
    (hz : ‖z‖ < 1) (hr : a.radius ≤ 1 / 4) :
    greenPotential a.logWeightedMeasure z ≤
      ∫⁻ θ in a.angles, ENNReal.ofReal (normalizedInnerGreenMajorant z θ) := by
  have hL := a.log_one_div_pos
  rw [greenPotential, CircularArc.logWeightedMeasure,
    MeasureTheory.lintegral_smul_measure]
  change ENNReal.ofReal (1 / Real.log (1 / a.radius)) *
      (∫⁻ ζ, diskGreenENNReal z ζ ∂Measure.map
        (fun θ ↦ radialPoint a.radius θ) (volume.restrict a.angles)) ≤ _
  rw [MeasureTheory.lintegral_map (measurable_diskGreenENNReal_right z)]
  · have hrp : Measurable (fun θ ↦ radialPoint a.radius θ) := by
      unfold radialPoint
      fun_prop
    have hmeasK : Measurable
        (fun θ ↦ diskGreenENNReal z (radialPoint a.radius θ)) :=
      (measurable_diskGreenENNReal_right z).comp hrp
    calc
      ENNReal.ofReal (1 / Real.log (1 / a.radius)) *
          (∫⁻ θ in a.angles, diskGreenENNReal z (radialPoint a.radius θ)) =
          ∫⁻ θ in a.angles, ENNReal.ofReal (1 / Real.log (1 / a.radius)) *
            diskGreenENNReal z (radialPoint a.radius θ) := by
        exact (MeasureTheory.lintegral_const_mul _ hmeasK).symm
      _ ≤ ∫⁻ θ in a.angles,
          ENNReal.ofReal (normalizedInnerGreenMajorant z θ) := by
        apply lintegral_mono_ae
        filter_upwards [ae_sin_sub_ne_zero z.arg a.angles] with θ hθ
        have hk := diskGreenENNReal_div_log_le_normalizedInnerGreenMajorant
          hz a.radius_pos hr hθ
        have hc : ENNReal.ofReal (1 / Real.log (1 / a.radius)) =
            1 / ENNReal.ofReal (Real.log (1 / a.radius)) := by
          have hc' := ENNReal.ofReal_div_of_pos (x := 1) hL
          simpa using hc'
        rw [hc]
        simpa [div_eq_mul_inv, mul_comm] using hk
  · unfold radialPoint
    fun_prop

/-- A finite family of pairwise angularly disjoint inner slits has uniformly bounded normalized
Green potential.  The bound `5 * π` is independent of the number, radii, and lengths of slits. -/
theorem greenPotential_logMeasure_le_inner
    (A : DisjointRadialArcs) {z : ℂ} (hz : ‖z‖ < 1)
    (hr : ∀ i, (A.arc i).radius ≤ 1 / 4)
    (hangle : A.angularSupport ⊆ angleDomain) :
    greenPotential A.logMeasure z ≤ ENNReal.ofReal (5 * Real.pi) := by
  rw [greenPotential, DisjointRadialArcs.logMeasure,
    MeasureTheory.lintegral_finsetSum_measure]
  change (∑ i, greenPotential (A.arc i).logWeightedMeasure z) ≤ _
  calc
    (∑ i, greenPotential (A.arc i).logWeightedMeasure z) ≤
        ∑ i, ∫⁻ θ in (A.arc i).angles,
          ENNReal.ofReal (normalizedInnerGreenMajorant z θ) := by
      exact Finset.sum_le_sum fun i _ ↦
        greenPotential_logWeightedMeasure_le_inner (A.arc i) hz (hr i)
    _ = ∫⁻ θ in A.angularSupport,
          ENNReal.ofReal (normalizedInnerGreenMajorant z θ) := by
      rw [DisjointRadialArcs.angularSupport,
        MeasureTheory.lintegral_iUnion
          (fun i ↦ (A.arc i).measurableSet_angles)
          (fun i j hij ↦ A.angle_disjoint (Set.mem_univ i) (Set.mem_univ j) hij),
        tsum_fintype]
    _ ≤ ∫⁻ θ in angleDomain,
          ENNReal.ofReal (normalizedInnerGreenMajorant z θ) :=
      MeasureTheory.lintegral_mono_set hangle
    _ = ENNReal.ofReal (5 * Real.pi) := lintegral_normalizedInnerGreenMajorant z

/-! ### Exact normalized integral at the self radius -/

lemma circleAverage_diskGreen_selfRadius {z : ℂ}
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    Real.circleAverage (fun w ↦ diskGreen z w) 0 ‖z‖ = Real.log (1 / ‖z‖) := by
  let ρ := ‖z‖
  let g : ℂ → ℂ := fun w ↦ 1 - (starRingEnd ℂ) z * w
  have hρ : 0 < ρ := norm_pos_iff.mpr hz0
  have hρ1 : ρ < 1 := hz
  have hgA : AnalyticOnNhd ℂ g (Metric.closedBall 0 |ρ|) := by
    intro w hw
    dsimp [g]
    fun_prop
  have hg0 : ∀ w ∈ Metric.closedBall (0 : ℂ) |ρ|, g w ≠ 0 := by
    intro w hw hzero
    have hwle : ‖w‖ ≤ ρ := by
      rw [Metric.mem_closedBall, dist_zero_right, abs_of_pos hρ] at hw
      exact hw
    have hp : ρ * ‖w‖ = 1 := by
      have heq : (starRingEnd ℂ) z * w = 1 := (sub_eq_zero.mp hzero).symm
      have ht := congrArg norm heq
      simpa [g, ρ, norm_mul, Complex.norm_conj] using ht
    have hlt : ρ * ‖w‖ < 1 := by
      calc
        ρ * ‖w‖ ≤ ρ * ρ := mul_le_mul_of_nonneg_left hwle hρ.le
        _ < 1 := by nlinarith
    linarith
  have hnumAvg : Real.circleAverage (fun w ↦ Real.log ‖g w‖) 0 ρ = 0 := by
    simpa [g] using hgA.circleAverage_log_norm_of_ne_zero hg0
  have hdenAvg : Real.circleAverage (fun w ↦ Real.log ‖w - z‖) 0 ρ =
      Real.log ρ := by
    apply circleAverage_log_norm_sub_const_of_mem_closedBall
    simp [ρ, abs_of_pos hρ]
  have hnumInt : CircleIntegrable (fun w ↦ Real.log ‖g w‖) 0 ρ := by
    exact (hgA.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hdenInt : CircleIntegrable (fun w ↦ Real.log ‖w - z‖) 0 ρ :=
    circleIntegrable_log_norm_sub_const ρ
  have hevent : (fun w ↦ diskGreen w z) =ᶠ[codiscreteWithin
      (Metric.sphere 0 |ρ|)]
      (fun w ↦ Real.log ‖g w‖ - Real.log ‖w - z‖) := by
    filter_upwards [compl_singleton_mem_codiscreteWithin
      (s := Metric.sphere (0 : ℂ) |ρ|) z,
      Filter.self_mem_codiscreteWithin (Metric.sphere (0 : ℂ) |ρ|)] with w hw hws
    have hwne : w ≠ z := by simpa using hw
    have hgw : g w ≠ 0 := hg0 w (Metric.sphere_subset_closedBall hws)
    rw [diskGreen, Real.log_div (norm_ne_zero_iff.mpr hgw)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwne))]
  have havg : Real.circleAverage (fun w ↦ diskGreen w z) 0 ρ =
      Real.log (1 / ρ) := by
    rw [Real.circleAverage_congr_codiscreteWithin hevent hρ.ne',
      Real.circleAverage_fun_sub hnumInt hdenInt, hnumAvg, hdenAvg]
    rw [Real.log_div (by norm_num) hρ.ne']
    simp
  simpa [ρ, diskGreen_comm] using havg

lemma circleIntegrable_diskGreen_selfRadius {z : ℂ}
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    CircleIntegrable (fun w ↦ diskGreen z w) 0 ‖z‖ := by
  let ρ := ‖z‖
  let g : ℂ → ℂ := fun w ↦ 1 - (starRingEnd ℂ) z * w
  have hρ : 0 < ρ := norm_pos_iff.mpr hz0
  have hgA : AnalyticOnNhd ℂ g (Metric.closedBall 0 |ρ|) := by
    intro w hw
    dsimp [g]
    fun_prop
  have hg0 : ∀ w ∈ Metric.closedBall (0 : ℂ) |ρ|, g w ≠ 0 := by
    intro w hw hzero
    have hwle : ‖w‖ ≤ ρ := by
      rw [Metric.mem_closedBall, dist_zero_right, abs_of_pos hρ] at hw
      exact hw
    have hp : ρ * ‖w‖ = 1 := by
      have heq : (starRingEnd ℂ) z * w = 1 := (sub_eq_zero.mp hzero).symm
      have ht := congrArg norm heq
      simpa [g, ρ, norm_mul, Complex.norm_conj] using ht
    have hlt : ρ * ‖w‖ < 1 := by
      calc
        ρ * ‖w‖ ≤ ρ * ρ := mul_le_mul_of_nonneg_left hwle hρ.le
        _ < 1 := by nlinarith
    linarith
  have hnumInt : CircleIntegrable (fun w ↦ Real.log ‖g w‖) 0 ρ :=
    (hgA.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hdenInt : CircleIntegrable (fun w ↦ Real.log ‖w - z‖) 0 ρ :=
    circleIntegrable_log_norm_sub_const ρ
  have hevent : (fun w ↦ diskGreen w z) =ᶠ[codiscreteWithin
      (Metric.sphere 0 |ρ|)]
      (fun w ↦ Real.log ‖g w‖ - Real.log ‖w - z‖) := by
    filter_upwards [compl_singleton_mem_codiscreteWithin
      (s := Metric.sphere (0 : ℂ) |ρ|) z,
      Filter.self_mem_codiscreteWithin (Metric.sphere (0 : ℂ) |ρ|)] with w hw hws
    have hwne : w ≠ z := by simpa using hw
    have hgw : g w ≠ 0 := hg0 w (Metric.sphere_subset_closedBall hws)
    rw [diskGreen, Real.log_div (norm_ne_zero_iff.mpr hgw)
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwne))]
  have hfirst : CircleIntegrable (fun w ↦ diskGreen w z) 0 ρ :=
    (hnumInt.sub hdenInt).congr_codiscreteWithin hevent.symm
  have hcomm : CircleIntegrable (fun w ↦ diskGreen z w) 0 ρ ↔
      CircleIntegrable (fun w ↦ diskGreen w z) 0 ρ :=
    circleIntegrable_congr fun w hw ↦ diskGreen_comm z w
  exact_mod_cast hcomm.mpr hfirst

lemma intervalIntegral_diskGreen_selfRadius {z : ℂ}
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), diskGreen z (radialPoint ‖z‖ θ) =
      2 * Real.pi * Real.log (1 / ‖z‖) := by
  have havg := circleAverage_diskGreen_selfRadius hz0 hz
  rw [Real.circleAverage_def] at havg
  simp only [smul_eq_mul] at havg
  have hmap : (fun θ : ℝ ↦ diskGreen z (circleMap 0 ‖z‖ θ)) =
      (fun θ : ℝ ↦ diskGreen z (radialPoint ‖z‖ θ)) := by
    funext θ
    simp [circleMap, radialPoint]
  rw [hmap] at havg
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), diskGreen z (radialPoint ‖z‖ θ)) =
        (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), diskGreen z (radialPoint ‖z‖ θ)) := by
      field_simp [Real.pi_ne_zero]
    _ = 2 * Real.pi * Real.log (1 / ‖z‖) := by rw [havg]

/-- At the self radius, the angular integral of the Green kernel normalized by its value at the
origin is exactly the full angular measure `2 * π`.  The diagonal Green pole lies over a null set
of angles and is therefore correctly represented by `diskGreenENNReal`. -/
theorem lintegral_diskGreenENNReal_selfRadius_normalized {z : ℂ}
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    ∫⁻ θ in angleDomain, diskGreenENNReal z (radialPoint ‖z‖ θ) /
        ENNReal.ofReal (Real.log (1 / ‖z‖)) =
      ENNReal.ofReal (2 * Real.pi) := by
  let ρ := ‖z‖
  let L := Real.log (1 / ρ)
  let F : ℝ → ℝ := fun θ ↦ diskGreen z (radialPoint ρ θ) / L
  have hρ : 0 < ρ := norm_pos_iff.mpr hz0
  have hL : 0 < L := Real.log_pos (one_lt_one_div hρ hz)
  have hcircleI : CircleIntegrable (fun w ↦ diskGreen z w) 0 ρ := by
    simpa [ρ] using circleIntegrable_diskGreen_selfRadius hz0 hz
  have hFI : IntervalIntegrable F volume 0 (2 * Real.pi) := by
    convert hcircleI.div_const L using 1
    ext θ
    simp [F, circleMap, radialPoint]
  have hle : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hFint : Integrable F (volume.restrict angleDomain) := by
    rw [angleDomain]
    exact (intervalIntegrable_iff_integrableOn_Ico_of_le hle).1 hFI
  have hF0 : ∀ θ, 0 ≤ F θ := by
    intro θ
    apply div_nonneg _ hL.le
    by_cases heq : z = radialPoint ρ θ
    · rw [heq]
      simp [diskGreen]
    · apply diskGreen_nonneg hz
        (by simp [ρ, radialPoint]; exact hz)
        heq
  have hreal : ∫ θ, F θ ∂volume.restrict angleDomain = 2 * Real.pi := by
    rw [angleDomain, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hle,
      intervalIntegral.integral_div]
    rw [show (∫ θ in (0 : ℝ)..(2 * Real.pi),
        diskGreen z (radialPoint ρ θ)) =
        2 * Real.pi * L by
      simpa [ρ, L] using intervalIntegral_diskGreen_selfRadius hz0 hz]
    field_simp
  have hae : ∀ᵐ θ ∂volume.restrict angleDomain,
      diskGreenENNReal z (radialPoint ρ θ) / ENNReal.ofReal L =
        ENNReal.ofReal (F θ) := by
    filter_upwards [ae_sin_sub_ne_zero z.arg angleDomain] with θ hθ
    have hne : z ≠ radialPoint ρ θ := by
      intro heq
      have htrans := norm_radialPoint_sub_ge_mul_abs_sin z ρ θ
      rw [heq] at htrans
      simp [radialPoint, abs_of_pos hρ] at htrans
      have hs0 : |Real.sin (θ - (radialPoint ρ θ).arg)| = 0 :=
        le_antisymm (nonpos_of_mul_nonpos_right htrans hρ) (abs_nonneg _)
      apply hθ
      rw [heq]
      exact abs_eq_zero.mp hs0
    rw [diskGreenENNReal_of_ne hne, ← ENNReal.ofReal_div_of_pos hL]
  rw [lintegral_congr_ae hae]
  rw [← ofReal_integral_eq_lintegral_ofReal hFint (ae_of_all _ hF0), hreal]

lemma one_sub_sq_le_two_mul_log_one_div {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    1 - r ^ 2 ≤ 2 * Real.log (1 / r) := by
  have h := one_sub_le_log_one_div hr
  have hgap : 0 ≤ 1 - r := by linarith
  have hr0 : 0 ≤ r := hr.le
  calc
    1 - r ^ 2 = (1 - r) * (1 + r) := by ring
    _ ≤ (1 - r) * 2 := by gcongr <;> linarith
    _ ≤ Real.log (1 / r) * 2 := by gcongr
    _ = 2 * Real.log (1 / r) := by ring

lemma norm_radialPoint_one_sub {r θ : ℝ} (hr : r ≤ 1) :
    ‖radialPoint 1 θ - radialPoint r θ‖ = 1 - r := by
  rw [show radialPoint 1 θ - radialPoint r θ =
      ((1-r : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) by
    unfold radialPoint
    push_cast
    ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (sub_nonneg.mpr hr)]
  simp

lemma norm_radialPoint_sub_same {r s θ : ℝ} :
    ‖radialPoint r θ - radialPoint s θ‖ = |r - s| := by
  rw [show radialPoint r θ - radialPoint s θ =
      ((r-s : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) by
    unfold radialPoint
    push_cast
    ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  simp

noncomputable def outerPoissonMajorant (z : ℂ) (θ : ℝ) : ℝ :=
  poissonKernel 0 z (radialPoint 1 θ)

noncomputable def outerSelfGreen (z : ℂ) (θ : ℝ) : ℝ≥0∞ :=
  diskGreenENNReal z (radialPoint ‖z‖ θ) /
    ENNReal.ofReal (Real.log (1 / ‖z‖))

lemma outerPoissonMajorant_nonneg {z : ℂ} (hz : ‖z‖ < 1) (θ : ℝ) :
    0 ≤ outerPoissonMajorant z θ := by
  rw [outerPoissonMajorant, poissonKernel_def]
  apply div_nonneg
  · simpa [norm_radialPoint (by norm_num : (0 : ℝ) ≤ 1)] using
      (sq_le_sq₀ (norm_nonneg z) (by norm_num : (0 : ℝ) ≤ 1)).2 hz.le
  · positivity

lemma diskGreen_div_log_le_poisson_far
    {z : ℂ} (hz : ‖z‖ < 1) {r θ : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hfar : (1 - ‖z‖) / 2 < ‖z - radialPoint r θ‖) :
    diskGreen z (radialPoint r θ) / Real.log (1 / r) ≤
      16 * outerPoissonMajorant z θ := by
  let ρ := ‖z‖
  let d := ‖z - radialPoint r θ‖
  let D := ‖radialPoint 1 θ - z‖
  have hL : 0 < Real.log (1 / r) := Real.log_pos (one_lt_one_div hr hr1)
  have hζ : ‖radialPoint r θ‖ < 1 := by simpa [norm_radialPoint hr.le]
  have hne : z ≠ radialPoint r θ := by
    intro h
    subst z
    simp only [sub_self, norm_zero] at hfar
    simp only [norm_radialPoint hr.le] at hfar
    linarith
  have hbase := diskGreen_le_greenQuotient hz hζ hne
  have hnum : 0 ≤ 1 - ρ ^ 2 := by
    dsimp [ρ]
    nlinarith [mul_nonneg (show 0 ≤ 1 - ‖z‖ by linarith)
      (show 0 ≤ 1 + ‖z‖ by positivity)]
  have hd : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hgreen : diskGreen z (radialPoint r θ) / Real.log (1 / r) ≤
      (1 - ρ ^ 2) / d ^ 2 := by
    calc
      diskGreen z (radialPoint r θ) / Real.log (1 / r) ≤
          (((1 - ρ ^ 2) * (1 - r ^ 2)) / (2 * d ^ 2)) /
            Real.log (1 / r) := by
        apply div_le_div_of_nonneg_right _ hL.le
        simpa [ρ, d, norm_radialPoint hr.le] using hbase
      _ ≤ (1 - ρ ^ 2) / d ^ 2 := by
        have hs := one_sub_sq_le_two_mul_log_one_div hr hr1
        have hmul := mul_le_mul_of_nonneg_left hs hnum
        field_simp
        nlinarith
  have hdr : |ρ - r| ≤ d := by
    dsimp [ρ, d]
    simpa [norm_radialPoint hr.le] using
      (abs_norm_sub_norm_le z (radialPoint r θ))
  have hs : 1 - r < 3 * d := by
    have ha : 1 - ρ < 2 * d := by
      dsimp [ρ, d]
      linarith
    have : 1-r = (1-ρ) + (ρ-r) := by ring
    rw [this]
    calc
      (1-ρ) + (ρ-r) ≤ (1-ρ) + |ρ-r| := by gcongr; exact le_abs_self _
      _ < 2*d+d := by linarith [hdr]
      _ = 3*d := by ring
  have hD : D < 4 * d := by
    have ht := norm_add_le (radialPoint 1 θ - radialPoint r θ)
      (radialPoint r θ - z)
    have heq : (radialPoint 1 θ - radialPoint r θ) +
        (radialPoint r θ - z) = radialPoint 1 θ - z := by ring
    rw [heq] at ht
    calc
      D ≤ ‖radialPoint 1 θ - radialPoint r θ‖ +
          ‖radialPoint r θ - z‖ := by simpa [D] using ht
      _ = (1-r)+d := by rw [norm_radialPoint_one_sub hr1.le]; simp [d, norm_sub_rev]
      _ < 4*d := by linarith
  have hDpos : 0 < D := by
    dsimp [D]
    rw [norm_pos_iff]
    intro h
    have hnorm : ‖radialPoint 1 θ‖ = 1 := norm_radialPoint (by norm_num)
    have heq : radialPoint 1 θ = z := sub_eq_zero.mp h
    have heqnorm := congrArg norm heq
    rw [hnorm] at heqnorm
    linarith
  calc
    diskGreen z (radialPoint r θ) / Real.log (1 / r) ≤
        (1-ρ^2)/d^2 := hgreen
    _ ≤ 16 * ((1-ρ^2)/D^2) := by
      have hsq : D ^ 2 ≤ 16 * d ^ 2 := by nlinarith [sq_nonneg (D - 4*d), hD]
      have hmul := mul_le_mul_of_nonneg_left hsq hnum
      field_simp
      nlinarith
    _ = 16 * ((1 ^ 2 - ρ ^ 2) / D ^ 2) := by norm_num
    _ = 16 * outerPoissonMajorant z θ := by
      unfold outerPoissonMajorant poissonKernel
      dsimp [ρ, D]
      simp [norm_radialPoint (by norm_num : (0 : ℝ) ≤ 1)]

lemma diskGreen_div_log_le_self_add_poisson_near
    {z : ℂ} (hz : ‖z‖ < 1) (hzlarge : 1 / 8 < ‖z‖) {r θ : ℝ}
    (hr : 0 < r) (hr1 : r < 1)
    (hnear : ‖z - radialPoint r θ‖ ≤ (1 - ‖z‖) / 2)
    (hself : z ≠ radialPoint ‖z‖ θ) :
    diskGreen z (radialPoint r θ) / Real.log (1 / r) ≤
      16 * (diskGreen z (radialPoint ‖z‖ θ) / Real.log (1 / ‖z‖)) +
        16 * outerPoissonMajorant z θ := by
  let ρ := ‖z‖
  let a := 1 - ρ
  let ζ := radialPoint r θ
  let η := radialPoint ρ θ
  let d := ‖z - ζ‖
  let d₀ := ‖z - η‖
  let D := ‖radialPoint 1 θ - z‖
  let N := ‖1 - (starRingEnd ℂ) ζ * z‖
  let N₀ := ‖1 - (starRingEnd ℂ) η * z‖
  let L := Real.log (1 / r)
  let L₀ := Real.log (1 / ρ)
  have hρ0 : 0 < ρ := by dsimp [ρ]; linarith
  have hρ1 : ρ < 1 := by simpa [ρ] using hz
  have ha : 0 < a := by dsimp [a]; linarith
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos (one_lt_one_div hr hr1)
  have hL₀ : 0 < L₀ := by dsimp [L₀]; exact Real.log_pos (one_lt_one_div hρ0 hρ1)
  have hζnorm : ‖ζ‖ = r := by dsimp [ζ]; exact norm_radialPoint hr.le
  have hηnorm : ‖η‖ = ρ := by dsimp [η]; exact norm_radialPoint hρ0.le
  have hζdisk : ‖ζ‖ < 1 := by rw [hζnorm]; exact hr1
  have hηdisk : ‖η‖ < 1 := by rw [hηnorm]; exact hρ1
  have hzne : z ≠ ζ := by
    intro heq
    have hnormeq : ρ = r := by
      dsimp [ρ]
      calc
        ‖z‖ = ‖ζ‖ := congrArg norm heq
        _ = r := hζnorm
    apply hself
    rw [heq]
    dsimp [η, ρ, ζ]
    rw [norm_radialPoint hr.le]
  have hd : 0 < d := by dsimp [d]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hzne)
  have hd₀ : 0 < d₀ := by dsimp [d₀, η]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hself)
  have hN : 0 < N := by
    dsimp [N]
    rw [norm_pos_iff]
    intro hzero
    have hp : ‖ζ‖ * ‖z‖ = 1 := by
      have heq : (starRingEnd ℂ) ζ * z = 1 := (sub_eq_zero.mp hzero).symm
      have := congrArg norm heq
      simpa [norm_mul, Complex.norm_conj] using this
    nlinarith [mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg ζ) hζdisk hz.le]
  have hN₀ : 0 < N₀ := by
    dsimp [N₀]
    rw [norm_pos_iff]
    intro hzero
    have hp : ‖η‖ * ‖z‖ = 1 := by
      have heq : (starRingEnd ℂ) η * z = 1 := (sub_eq_zero.mp hzero).symm
      have := congrArg norm heq
      simpa [norm_mul, Complex.norm_conj] using this
    rw [hηnorm] at hp
    nlinarith
  have hdr : |ρ - r| ≤ d := by
    dsimp [ρ, d, ζ]
    simpa [norm_radialPoint hr.le] using
      (abs_norm_sub_norm_le z (radialPoint r θ))
  have hradial : ‖η - ζ‖ = |ρ - r| := by
    dsimp [η, ζ]
    exact norm_radialPoint_sub_same
  have hd₀le : d₀ ≤ 2 * d := by
    have ht := norm_add_le (z - ζ) (ζ - η)
    have heq : (z-ζ)+(ζ-η)=z-η := by ring
    rw [heq] at ht
    calc
      d₀ ≤ d + ‖ζ-η‖ := by simpa [d₀, d] using ht
      _ = d + |ρ-r| := by rw [norm_sub_rev, hradial]
      _ ≤ 2*d := by linarith
  have hN₀lower : a ≤ N₀ := by
    have ht := norm_sub_norm_le (1 : ℂ) ((starRingEnd ℂ) η * z)
    have hprod : ‖(starRingEnd ℂ) η * z‖ = ρ ^ 2 := by
      rw [norm_mul, Complex.norm_conj, hηnorm]
      dsimp [ρ]
      ring
    have hraw : 1 - ρ^2 ≤ N₀ := by
      dsimp [N₀]
      rw [norm_one, hprod] at ht
      linarith [le_abs_self (1-ρ^2)]
    dsimp [a]
    nlinarith [mul_nonneg (show 0 ≤ 1-ρ by linarith)
      (show 0 ≤ ρ by exact hρ0.le)]
  have hNle : N ≤ (3/2 : ℝ) * N₀ := by
    have hdecomp : 1 - (starRingEnd ℂ) ζ * z =
        (1 - (starRingEnd ℂ) η * z) +
          (((starRingEnd ℂ) η - (starRingEnd ℂ) ζ) * z) := by ring
    have ht := norm_add_le (1 - (starRingEnd ℂ) η * z)
      (((starRingEnd ℂ) η - (starRingEnd ℂ) ζ) * z)
    rw [← hdecomp] at ht
    have hdiff : ‖((starRingEnd ℂ) η - (starRingEnd ℂ) ζ) * z‖ ≤ d := by
      rw [norm_mul, ← map_sub, Complex.norm_conj, hradial]
      have hρle : ρ ≤ 1 := hρ1.le
      exact (mul_le_of_le_one_right (abs_nonneg _) hρle).trans hdr
    have hdhalf : d ≤ N₀ / 2 := by
      have := hnear
      change d ≤ a / 2 at this
      linarith
    change N ≤ _
    dsimp [N, N₀] at ht ⊢
    linarith
  have hratio : N / d ≤ 3 * (N₀ / d₀) := by
    have hprod : N * d₀ ≤ 3 * N₀ * d := by
      nlinarith [mul_le_mul hNle hd₀le (norm_nonneg _)
        (by positivity : 0 ≤ (3/2:ℝ) * N₀)]
    field_simp
    nlinarith
  have hgreenCompare : diskGreen z ζ ≤ diskGreen z η + Real.log 3 := by
    rw [diskGreen, diskGreen]
    have hratioPos : 0 < N/d := div_pos hN hd
    have hselfRatioPos : 0 < N₀/d₀ := div_pos hN₀ hd₀
    calc
      Real.log (‖1-(starRingEnd ℂ) ζ*z‖ / ‖z-ζ‖) = Real.log (N/d) := by rfl
      _ ≤ Real.log (3 * (N₀/d₀)) :=
        Real.strictMonoOn_log.monotoneOn hratioPos (mul_pos (by norm_num) hselfRatioPos) hratio
      _ = Real.log (N₀/d₀) + Real.log 3 := by
        rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hselfRatioPos.ne']
        ring
      _ = Real.log (‖1-(starRingEnd ℂ) η*z‖ / ‖z-η‖) + Real.log 3 := by rfl
  have hselfnonneg : 0 ≤ diskGreen z η := diskGreen_nonneg hz hηdisk hself
  have hLcomp : L₀ ≤ 16 * L := by
    have hL₀upper : L₀ ≤ a / ρ := by
      have hh := Real.log_le_sub_one_of_pos (one_div_pos.mpr hρ0)
      dsimp [L₀]
      calc
        Real.log (1/ρ) ≤ 1/ρ-1 := hh
        _ = a/ρ := by dsimp [a]; field_simp
    have hsLower : a/2 ≤ 1-r := by
      have : |ρ-r| ≤ a/2 := hdr.trans hnear
      dsimp [a]
      linarith [neg_abs_le (ρ-r)]
    have hLlower : 1-r ≤ L := by
      dsimp [L]
      exact one_sub_le_log_one_div hr
    have ha8 : a/ρ < 8*a := by
      rw [div_lt_iff₀ hρ0]
      nlinarith [hzlarge]
    linarith
  have hDle : D ≤ 2*a := by
    have hsUpper : 1-r ≤ a+d := by
      dsimp [a]
      linarith [hdr, le_abs_self (ρ-r)]
    have ht := norm_add_le (radialPoint 1 θ - ζ) (ζ-z)
    have heq : (radialPoint 1 θ-ζ)+(ζ-z)=radialPoint 1 θ-z := by ring
    rw [heq] at ht
    calc
      D ≤ ‖radialPoint 1 θ-ζ‖+‖ζ-z‖ := by simpa [D] using ht
      _ = (1-r)+d := by
        dsimp [ζ]
        rw [norm_radialPoint_one_sub hr1.le]
        dsimp [d]
        rw [norm_sub_rev]
      _ ≤ 2*a := by linarith [hnear]
  have hDpos : 0 < D := by
    dsimp [D]
    rw [norm_pos_iff]
    intro h
    have heq : radialPoint 1 θ = z := sub_eq_zero.mp h
    have heqnorm := congrArg norm heq
    rw [norm_radialPoint (by norm_num : (0:ℝ)≤1)] at heqnorm
    linarith
  have hpoisson : 2 * Real.log 3 / a ≤ 16 * outerPoissonMajorant z θ := by
    have hlog3 : Real.log 3 ≤ 2 := by
      convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3) using 1 <;> norm_num
    have hsq : D^2 ≤ 4*a^2 := by nlinarith [sq_nonneg (D-2*a), hDle]
    have hnum : a ≤ 1-ρ^2 := by
      dsimp [a]
      nlinarith [mul_nonneg (show 0≤1-ρ by linarith) (show 0≤ρ by exact hρ0.le)]
    unfold outerPoissonMajorant poissonKernel
    simp only [sub_zero, norm_radialPoint (by norm_num : (0:ℝ)≤1), one_pow]
    change 2*Real.log 3/a ≤ 16*((1-ρ^2)/D^2)
    have hleft : 2*Real.log 3/a ≤ 4/a := by
      apply div_le_div_of_nonneg_right _ ha.le
      nlinarith
    apply hleft.trans
    field_simp
    nlinarith
  calc
    diskGreen z ζ / L ≤ (diskGreen z η + Real.log 3) / L :=
      div_le_div_of_nonneg_right hgreenCompare hL.le
    _ = diskGreen z η / L + Real.log 3 / L := by ring
    _ ≤ 16 * (diskGreen z η / L₀) + 2*Real.log 3/a := by
      have hfirst : diskGreen z η / L ≤ 16*(diskGreen z η/L₀) := by
        rw [show 16 * (diskGreen z η / L₀) =
          (16 * diskGreen z η) / L₀ by ring, div_le_div_iff₀ hL hL₀]
        have hm := mul_le_mul_of_nonneg_left hLcomp hselfnonneg
        nlinarith only [hm]
      have hsecond : Real.log 3 / L ≤ 2*Real.log 3/a := by
        have hlog3nonneg : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
        have hLlower : a/2 ≤ L := by
          have hsLower : a/2 ≤ 1-r := by
            have : |ρ-r| ≤ a/2 := hdr.trans hnear
            dsimp [a]
            linarith [neg_abs_le (ρ-r)]
          exact hsLower.trans (by dsimp [L]; exact one_sub_le_log_one_div hr)
        rw [show 2 * Real.log 3 / a = (2 * Real.log 3) / a by ring,
          div_le_div_iff₀ hL ha]
        have ha2L : a ≤ 2*L := by linarith only [hLlower]
        have hm := mul_le_mul_of_nonneg_left ha2L hlog3nonneg
        nlinarith only [hm]
      linarith
    _ ≤ 16*(diskGreen z η/L₀)+16*outerPoissonMajorant z θ := by gcongr
    _ = _ := by rfl


noncomputable def outerNormalizedGreenMajorant (z : ℂ) (θ : ℝ) : ℝ≥0∞ :=
  if ‖z‖ ≤ 1 / 8 then 64 else
    16 * outerSelfGreen z θ +
      16 * ENNReal.ofReal (outerPoissonMajorant z θ)

lemma diskGreenENNReal_div_log_le_outerNormalizedGreenMajorant
    {z : ℂ} (hz : ‖z‖ < 1) {r θ : ℝ}
    (hr : 1 / 4 ≤ r) (hr1 : r < 1) :
    diskGreenENNReal z (radialPoint r θ) /
        ENNReal.ofReal (Real.log (1 / r)) ≤
      outerNormalizedGreenMajorant z θ := by
  have hr0 : 0 < r := (by norm_num : (0 : ℝ) < 1/4).trans_le hr
  have hL : 0 < Real.log (1/r) := Real.log_pos (one_lt_one_div hr0 hr1)
  by_cases hzsmall : ‖z‖ ≤ 1/8
  · rw [outerNormalizedGreenMajorant, if_pos hzsmall]
    have hne : z ≠ radialPoint r θ := by
      intro heq
      have heqnorm := congrArg norm heq
      rw [norm_radialPoint hr0.le] at heqnorm
      linarith
    rw [diskGreenENNReal_of_ne hne, ← ENNReal.ofReal_div_of_pos hL]
    have h64 : (64 : ℝ≥0∞) = ENNReal.ofReal (64 : ℝ) := by norm_num
    rw [h64]
    apply ENNReal.ofReal_le_ofReal
    let d := ‖z-radialPoint r θ‖
    have hd : 0 < d := by dsimp [d]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hζ : ‖radialPoint r θ‖ < 1 := by simpa [norm_radialPoint hr0.le]
    have hbase := diskGreen_le_greenQuotient hz hζ hne
    have hnum : 0 ≤ 1-‖z‖^2 := by
      nlinarith [mul_nonneg (show 0≤1-‖z‖ by linarith)
        (show 0≤1+‖z‖ by positivity)]
    have hgreen : diskGreen z (radialPoint r θ) / Real.log (1/r) ≤
        (1-‖z‖^2)/d^2 := by
      calc
        diskGreen z (radialPoint r θ) / Real.log (1/r) ≤
            (((1-‖z‖^2)*(1-r^2))/(2*d^2))/Real.log (1/r) := by
          apply div_le_div_of_nonneg_right _ hL.le
          simpa [d, norm_radialPoint hr0.le] using hbase
        _ ≤ (1-‖z‖^2)/d^2 := by
          have hs := one_sub_sq_le_two_mul_log_one_div hr0 hr1
          have hm := mul_le_mul_of_nonneg_left hs hnum
          field_simp
          nlinarith
    have hdist : 1/8 ≤ d := by
      have ht := abs_norm_sub_norm_le z (radialPoint r θ)
      have : r-‖z‖ ≤ d := by
        calc
          r-‖z‖ ≤ |r-‖z‖| := le_abs_self _
          _ = |‖z‖-r| := abs_sub_comm _ _
          _ ≤ d := by
            dsimp [d]
            simpa [norm_radialPoint hr0.le] using ht
      linarith
    have hd2 : 1/64 ≤ d^2 := by nlinarith [sq_nonneg (d-1/8)]
    exact hgreen.trans (by
      rw [div_le_iff₀ (sq_pos_of_pos hd)]
      nlinarith [sq_nonneg ‖z‖])
  · rw [outerNormalizedGreenMajorant, if_neg hzsmall]
    have hzlarge : 1/8 < ‖z‖ := lt_of_not_ge hzsmall
    let η := radialPoint ‖z‖ θ
    by_cases hself : z = η
    · have htop : outerSelfGreen z θ = ⊤ := by
        unfold outerSelfGreen
        have heta : radialPoint ‖z‖ θ = z := hself.symm
        rw [heta, diskGreenENNReal_self]
        exact ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top
      rw [htop]
      simp
    · have hne : z ≠ radialPoint r θ := by
        intro heq
        apply hself
        have hnorm : ‖z‖ = r := by
          rw [heq, norm_radialPoint hr0.le]
        rw [heq]
        dsimp [η]
        rw [hnorm]
      rw [diskGreenENNReal_of_ne hne, ← ENNReal.ofReal_div_of_pos hL]
      have hselfL : 0 < Real.log (1/‖z‖) :=
        Real.log_pos (one_lt_one_div (by linarith) hz)
      have hselfENN : outerSelfGreen z θ =
          ENNReal.ofReal (diskGreen z η / Real.log (1/‖z‖)) := by
        unfold outerSelfGreen
        rw [diskGreenENNReal_of_ne hself, ← ENNReal.ofReal_div_of_pos hselfL]
      have hselfnonnegReal : 0 ≤ diskGreen z η / Real.log (1/‖z‖) := by
        exact div_nonneg (diskGreen_nonneg hz (by
          simpa [η, norm_radialPoint (norm_nonneg z)] using hz) hself) hselfL.le
      have hpoissonnonnegReal : 0 ≤ outerPoissonMajorant z θ :=
        outerPoissonMajorant_nonneg hz θ
      have h16 : (16 : ℝ≥0∞) = ENNReal.ofReal (16 : ℝ) := by norm_num
      rw [hselfENN, h16, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤16),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤16),
        ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hselfnonnegReal)
          (mul_nonneg (by norm_num) hpoissonnonnegReal)]
      apply ENNReal.ofReal_le_ofReal
      by_cases hfar : (1-‖z‖)/2 < ‖z-radialPoint r θ‖
      · have h := diskGreen_div_log_le_poisson_far hz hr0 hr1 hfar
        linarith
      · have hnear : ‖z-radialPoint r θ‖ ≤ (1-‖z‖)/2 := le_of_not_gt hfar
        exact diskGreen_div_log_le_self_add_poisson_near hz hzlarge hr0 hr1 hnear hself



end Erdos515
