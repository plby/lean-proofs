/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.Hall
import ErdosProblems.Erdos515.PrawitzProof
import ErdosProblems.Erdos515.KoebeDistortion
import ErdosProblems.Erdos515.RadialVariation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The logarithmic-derivative exceptional set

This file proves the logarithmic-area estimate used in the Lewis--Rossi--Weitsman short-path
argument.  All radial integrals take values in `ℝ≥0∞`, so divergence on an individual exceptional
ray is represented honestly rather than being hidden by the convention for non-integrable real
functions.
-/

open Metric MeasureTheory Set
open scoped ENNReal Real Topology

noncomputable section

namespace Erdos515
namespace LogDerivative

open Prawitz

/-- The radial logarithmic-derivative integral. -/
def logRadialIntegralE (G : ℂ → ℂ) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Ioc (0 : ℝ) 1,
    ENNReal.ofReal
      (r * ‖deriv G (circlePoint r θ)‖ / ‖G (circlePoint r θ)‖)

/-- A uniform planar logarithmic-area bound.  The deliberately generous constant comes from
Young's inequality on the regions `‖G‖ < 1` and `1 ≤ ‖G‖`. -/
def logAreaConstant : ℝ :=
  12 * Real.pi

/-- A fixed Chebyshev threshold making the logarithmic exceptional set smaller than `π / 4`. -/
def logThreshold : ℝ :=
  1 + 4 * logAreaConstant / Real.pi

lemma hardyQuarterConstant_pos : 0 < hardyQuarterConstant := by
  unfold hardyQuarterConstant
  apply lt_max_of_lt_left
  positivity

lemma logAreaConstant_pos : 0 < logAreaConstant := by
  unfold logAreaConstant
  positivity

lemma logThreshold_pos : 0 < logThreshold := by
  unfold logThreshold
  have hA := logAreaConstant_pos
  have hpi := Real.pi_pos
  positivity

lemma logThreshold_nonneg : 0 ≤ logThreshold := logThreshold_pos.le

/-- The explicit logarithmic-derivative exceptional set. -/
def logBad (G : ℂ → ℂ) : Set ℝ :=
  {θ | θ ∈ angleDomain ∧ ENNReal.ofReal logThreshold < logRadialIntegralE G θ}

/-- Outside `logBad`, the defining radial integral is at most the fixed threshold. -/
lemma logRadialIntegralE_le_of_not_mem_logBad {G : ℂ → ℂ} {θ : ℝ}
    (hθ : θ ∈ angleDomain) (hbad : θ ∉ logBad G) :
    logRadialIntegralE G θ ≤ ENNReal.ofReal logThreshold := by
  exact le_of_not_gt fun h ↦ hbad ⟨hθ, h⟩

/-- The elementary polar integral used on the region where `‖G‖ < 1`. -/
lemma lintegral_ball_inv_norm :
    (∫⁻ z : ℂ in ball 0 1, ENNReal.ofReal (1 / ‖z‖)) =
      ENNReal.ofReal (2 * Real.pi) := by
  classical
  let f : ℂ → ℝ≥0∞ := (ball (0 : ℂ) 1).indicator
    (fun z ↦ ENNReal.ofReal (1 / ‖z‖))
  have hpolar := Complex.lintegral_comp_polarCoord_symm f
  rw [← lintegral_indicator measurableSet_ball]
  change (∫⁻ z : ℂ, f z) = _
  rw [← hpolar, polarCoord_target]
  let T : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
  rw [← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  calc
    (∫⁻ p : ℝ × ℝ, T.indicator
        (fun p ↦ ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) p) =
        ∫⁻ p : ℝ × ℝ, S.indicator (fun _ ↦ (1 : ℝ≥0∞)) p := by
      apply lintegral_congr
      intro p
      by_cases hpT : p ∈ T
      · by_cases hr : p.1 < 1
        · have hpS : p ∈ S := ⟨⟨hpT.1, hr⟩, hpT.2⟩
          rw [Set.indicator_of_mem hpT, Set.indicator_of_mem hpS]
          have hp : 0 < p.1 := by exact hpT.1
          have hnorm : ‖(Complex.polarCoord.symm p : ℂ)‖ = p.1 := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hp]
          have hball : (Complex.polarCoord.symm p : ℂ) ∈ ball 0 1 := by
            simpa only [mem_ball, dist_zero_right, hnorm] using hr
          dsimp [f]
          rw [Set.indicator_of_mem hball]
          rw [← ENNReal.ofReal_mul hp.le, hnorm]
          field_simp
          simp
        · have hpS : p ∉ S := by
            intro h
            exact hr h.1.2
          rw [Set.indicator_of_mem hpT, Set.indicator_of_notMem hpS]
          have hp : 0 < p.1 := by exact hpT.1
          have hnorm : ‖(Complex.polarCoord.symm p : ℂ)‖ = p.1 := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hp]
          have hball : (Complex.polarCoord.symm p : ℂ) ∉ ball 0 1 := by
            simpa only [mem_ball, dist_zero_right, hnorm] using hr
          dsimp [f]
          rw [Set.indicator_of_notMem hball]
          simp
      · have hpS : p ∉ S := by
          intro h
          exact hpT ⟨h.1.1, h.2⟩
        rw [Set.indicator_of_notMem hpT, Set.indicator_of_notMem hpS]
    _ = volume S := by
      exact lintegral_indicator_one (measurableSet_Ioo.prod measurableSet_Ioo)
    _ = ENNReal.ofReal (2 * Real.pi) := by
      change (volume.prod volume) (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi) = _
      rw [Measure.prod_prod]
      simp [Real.volume_Ioo]
      rw [← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

lemma lintegral_Ioc_angle_shift_of_periodic {H : ℝ → ℝ≥0∞}
    (hH : Function.Periodic H (2 * Real.pi)) :
    (∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), H θ) =
      ∫⁻ θ in Ioc (-Real.pi) Real.pi, H θ := by
  letI : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  let f : AddCircle (2 * Real.pi) → ℝ≥0∞ := hH.lift
  have h0 := AddCircle.lintegral_preimage (T := 2 * Real.pi) 0 f
  have hneg := AddCircle.lintegral_preimage (T := 2 * Real.pi) (-Real.pi) f
  calc
    (∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi), H θ) =
        ∫⁻ a : AddCircle (2 * Real.pi), f a := by
      simpa only [zero_add, f, hH.lift_coe] using h0
    _ = ∫⁻ θ in Ioc (-Real.pi) (-Real.pi + 2 * Real.pi), f θ := hneg.symm
    _ = ∫⁻ θ in Ioc (-Real.pi) Real.pi, H θ := by
      congr 1
      ring

lemma polarCoord_symm_eq_circlePoint (r θ : ℝ) :
    (Complex.polarCoord.symm (r, θ) : ℂ) = circlePoint r θ := by
  rw [Complex.polarCoord_symm_apply]
  unfold circlePoint
  rw [Complex.exp_mul_I]
  push_cast
  ring

lemma lintegral_ball_eq_polar_Ioo (q : ℂ → ℝ≥0∞) (hq : Measurable q) :
    (∫⁻ z : ℂ in ball 0 1, q z) =
      ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ∫⁻ r in Ioo (0 : ℝ) 1, ENNReal.ofReal r * q (circlePoint r θ) := by
  let f : ℂ → ℝ≥0∞ := (ball (0 : ℂ) 1).indicator q
  have hpolar := Complex.lintegral_comp_polarCoord_symm f
  rw [← lintegral_indicator measurableSet_ball]
  change (∫⁻ z : ℂ, f z) = _
  rw [← hpolar, polarCoord_target]
  let T : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
  rw [← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  calc
    (∫⁻ p : ℝ × ℝ, T.indicator
        (fun p ↦ ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) p) =
        ∫⁻ p : ℝ × ℝ in S,
          ENNReal.ofReal p.1 * q (circlePoint p.1 p.2) := by
      rw [← lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
      apply lintegral_congr
      intro p
      by_cases hpT : p ∈ T
      · have hr0 : 0 < p.1 := hpT.1
        by_cases hr1 : p.1 < 1
        · have hpS : p ∈ S := ⟨⟨hr0, hr1⟩, hpT.2⟩
          rw [Set.indicator_of_mem hpT, Set.indicator_of_mem hpS]
          have hnorm : ‖(Complex.polarCoord.symm p : ℂ)‖ = p.1 := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hr0]
          have hball : (Complex.polarCoord.symm p : ℂ) ∈ ball 0 1 := by
            simpa only [mem_ball, dist_zero_right, hnorm] using hr1
          dsimp [f]
          rw [Set.indicator_of_mem hball]
          change ENNReal.ofReal p.1 * q (Complex.polarCoord.symm p) = _
          rw [polarCoord_symm_eq_circlePoint]
        · have hpS : p ∉ S := fun h ↦ hr1 h.1.2
          rw [Set.indicator_of_mem hpT, Set.indicator_of_notMem hpS]
          have hnorm : ‖(Complex.polarCoord.symm p : ℂ)‖ = p.1 := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hr0]
          have hball : (Complex.polarCoord.symm p : ℂ) ∉ ball 0 1 := by
            simpa only [mem_ball, dist_zero_right, hnorm] using hr1
          dsimp [f]
          rw [Set.indicator_of_notMem hball]
          simp
      · have hpS : p ∉ S := fun h ↦ hpT ⟨h.1.1, h.2⟩
        rw [Set.indicator_of_notMem hpT, Set.indicator_of_notMem hpS]
    _ = ∫⁻ θ in Ioo (-Real.pi) Real.pi,
          ∫⁻ r in Ioo (0 : ℝ) 1,
            ENNReal.ofReal r * q (circlePoint r θ) := by
      apply MeasureTheory.setLIntegral_prod_symm
      have hpoint : Measurable (fun p : ℝ × ℝ ↦ circlePoint p.1 p.2) := by
        unfold circlePoint
        fun_prop
      exact ((ENNReal.continuous_ofReal.comp continuous_fst).measurable.mul
        (hq.comp hpoint)).aemeasurable

/-- Polar coordinates over the standard angular interval used by the LRW construction. -/
lemma lintegral_ball_eq_polar (q : ℂ → ℝ≥0∞) (hq : Measurable q) :
    (∫⁻ z : ℂ in ball 0 1, q z) =
      ∫⁻ θ in Ioc (0 : ℝ) (2 * Real.pi),
        ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal r * q (circlePoint r θ) := by
  have hpolar := lintegral_ball_eq_polar_Ioo q hq
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hpolar
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hpolar
  let H : ℝ → ℝ≥0∞ := fun θ ↦
    ∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal r * q (circlePoint r θ)
  have hH : Function.Periodic H (2 * Real.pi) := by
    intro θ
    dsimp [H]
    apply lintegral_congr
    intro r
    congr 2
    unfold circlePoint
    push_cast
    rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  rw [hpolar]
  exact (lintegral_Ioc_angle_shift_of_periodic hH).symm

/-- The second elementary target-space integral used in the logarithmic-area estimate. -/
lemma lintegral_compl_ball_inv_norm_rpow :
    (∫⁻ z : ℂ in {z | 1 ≤ ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-(9 : ℝ) / 4))) =
      ENNReal.ofReal (8 * Real.pi) := by
  classical
  let U : Set ℂ := {z | 1 ≤ ‖z‖}
  let f : ℂ → ℝ≥0∞ := U.indicator
    (fun z ↦ ENNReal.ofReal (‖z‖ ^ (-(9 : ℝ) / 4)))
  have hpolar := Complex.lintegral_comp_polarCoord_symm f
  have hU : MeasurableSet U := by
    exact measurableSet_le continuous_const.measurable continuous_norm.measurable
  rw [← lintegral_indicator hU]
  change (∫⁻ z : ℂ, f z) = _
  rw [← hpolar, polarCoord_target]
  let T : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  let S : Set (ℝ × ℝ) := Ici (1 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  rw [← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  calc
    (∫⁻ p : ℝ × ℝ, T.indicator
        (fun p ↦ ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) p) =
        ∫⁻ p : ℝ × ℝ in S, ENNReal.ofReal (p.1 ^ (-(5 : ℝ) / 4)) := by
      rw [← lintegral_indicator (measurableSet_Ici.prod measurableSet_Ioo)]
      apply lintegral_congr
      intro p
      by_cases hpT : p ∈ T
      · have hp : 0 < p.1 := hpT.1
        by_cases hr : 1 ≤ p.1
        · have hpS : p ∈ S := ⟨hr, hpT.2⟩
          rw [Set.indicator_of_mem hpT, Set.indicator_of_mem hpS]
          have hnorm : ‖(Complex.polarCoord.symm p : ℂ)‖ = p.1 := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hp]
          have hpU : (Complex.polarCoord.symm p : ℂ) ∈ U := by
            change 1 ≤ ‖(Complex.polarCoord.symm p : ℂ)‖
            rwa [hnorm]
          dsimp [f]
          rw [Set.indicator_of_mem hpU, hnorm]
          rw [← ENNReal.ofReal_mul hp.le]
          congr 1
          calc
            p.1 * p.1 ^ (-(9 : ℝ) / 4) =
                p.1 ^ (1 : ℝ) * p.1 ^ (-(9 : ℝ) / 4) := by rw [Real.rpow_one]
            _ = p.1 ^ ((1 : ℝ) + (-(9 : ℝ) / 4)) := (Real.rpow_add hp _ _).symm
            _ = p.1 ^ (-(5 : ℝ) / 4) := by congr 1; ring
        · have hpS : p ∉ S := fun h ↦ hr h.1
          rw [Set.indicator_of_mem hpT, Set.indicator_of_notMem hpS]
          have hnorm : ‖(Complex.polarCoord.symm p : ℂ)‖ = p.1 := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hp]
          have hpU : (Complex.polarCoord.symm p : ℂ) ∉ U := by
            intro h
            exact hr (hnorm ▸ h)
          dsimp [f]
          rw [Set.indicator_of_notMem hpU]
          simp
      · have hpS : p ∉ S := by
          intro h
          have hp : 0 < p.1 := lt_of_lt_of_le zero_lt_one h.1
          exact hpT ⟨hp, h.2⟩
        rw [Set.indicator_of_notMem hpT, Set.indicator_of_notMem hpS]
    _ = ∫⁻ r : ℝ in Ici 1,
        ENNReal.ofReal (r ^ (-(5 : ℝ) / 4)) * volume (Ioo (-Real.pi) Real.pi) := by
      change (∫⁻ p : ℝ × ℝ in Ici (1 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal (p.1 ^ (-(5 : ℝ) / 4))) = _
      rw [Measure.volume_eq_prod, MeasureTheory.setLIntegral_prod]
      · apply lintegral_congr
        intro r
        simp only [Prod.fst]
        rw [MeasureTheory.setLIntegral_const]
      · fun_prop
    _ = ENNReal.ofReal (8 * Real.pi) := by
      have hint : IntegrableOn (fun r : ℝ ↦ r ^ (-(5 : ℝ) / 4)) (Ioi 1) :=
        integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
      have hrad : (∫⁻ r : ℝ in Ici 1, ENNReal.ofReal (r ^ (-(5 : ℝ) / 4))) =
          ENNReal.ofReal 4 := by
        rw [← setLIntegral_congr (Ioi_ae_eq_Ici' (by simp : volume ({1} : Set ℝ) = 0))]
        have hnonneg : ∀ᵐ r ∂volume.restrict (Ioi (1 : ℝ)),
            0 ≤ r ^ (-(5 : ℝ) / 4) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          exact Real.rpow_nonneg (zero_le_one.trans hr.le) _
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
        rw [integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
        norm_num
      rw [Real.volume_Ioo]
      rw [MeasureTheory.lintegral_mul_const]
      rw [hrad]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      apply congrArg ENNReal.ofReal
      ring
      fun_prop

/-- The target-space kernel on the part of the image lying in the unit disk. -/
def innerTargetKernel (w : ℂ) : ℝ≥0∞ :=
  (ball (0 : ℂ) 1).indicator (fun w ↦ ENNReal.ofReal (1 / ‖w‖)) w

/-- The integrable target-space kernel on the part of the image outside the unit disk. -/
def outerTargetKernel (w : ℂ) : ℝ≥0∞ :=
  {w : ℂ | 1 ≤ ‖w‖}.indicator
    (fun w ↦ ENNReal.ofReal (‖w‖ ^ (-(9 : ℝ) / 4))) w

lemma innerTargetKernel_lintegral :
    (∫⁻ w : ℂ, innerTargetKernel w) = ENNReal.ofReal (2 * Real.pi) := by
  change (∫⁻ w : ℂ, (ball (0 : ℂ) 1).indicator
    (fun w ↦ ENNReal.ofReal (1 / ‖w‖)) w) = _
  rw [lintegral_indicator measurableSet_ball]
  exact lintegral_ball_inv_norm

lemma outerTargetKernel_lintegral :
    (∫⁻ w : ℂ, outerTargetKernel w) = ENNReal.ofReal (8 * Real.pi) := by
  change (∫⁻ w : ℂ, {w : ℂ | 1 ≤ ‖w‖}.indicator
    (fun w ↦ ENNReal.ofReal (‖w‖ ^ (-(9 : ℝ) / 4))) w) = _
  rw [lintegral_indicator]
  · exact lintegral_compl_ball_inv_norm_rpow
  · exact measurableSet_le continuous_const.measurable continuous_norm.measurable

/-- Change of variables and injectivity bound the inner target-space term by `2π`. -/
lemma lintegral_jacobian_inner_le {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1)) :
    (∫⁻ z : ℂ in ball 0 1,
      ENNReal.ofReal (‖deriv G z‖ ^ 2) * innerTargetKernel (G z)) ≤
        ENNReal.ofReal (2 * Real.pi) := by
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := volume) (f := G) (f' := fun z ↦ fderiv ℝ G z)
    measurableSet_ball
    (fun z hz ↦ (hG z hz).restrictScalars.hasStrictFDerivAt.hasFDerivAt.hasFDerivWithinAt)
    hinj innerTargetKernel
  have hdet : ∀ z ∈ ball (0 : ℂ) 1,
      |(fderiv ℝ G z).det| = ‖deriv G z‖ ^ 2 := by
    intro z hz
    rw [Complex.fderiv_det (hG z hz).differentiableAt, abs_of_nonneg (sq_nonneg _)]
  rw [setLIntegral_congr_fun measurableSet_ball (fun z hz ↦ by rw [hdet z hz])] at hcov
  rw [← hcov]
  calc
    (∫⁻ w : ℂ in G '' ball 0 1, innerTargetKernel w) ≤
        ∫⁻ w : ℂ, innerTargetKernel w := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (2 * Real.pi) := innerTargetKernel_lintegral

/-- Change of variables and injectivity bound the exterior target-space term by `8π`. -/
lemma lintegral_jacobian_outer_le {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1)) :
    (∫⁻ z : ℂ in ball 0 1,
      ENNReal.ofReal (‖deriv G z‖ ^ 2) * outerTargetKernel (G z)) ≤
        ENNReal.ofReal (8 * Real.pi) := by
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (μ := volume) (f := G) (f' := fun z ↦ fderiv ℝ G z)
    measurableSet_ball
    (fun z hz ↦ (hG z hz).restrictScalars.hasStrictFDerivAt.hasFDerivAt.hasFDerivWithinAt)
    hinj outerTargetKernel
  have hdet : ∀ z ∈ ball (0 : ℂ) 1,
      |(fderiv ℝ G z).det| = ‖deriv G z‖ ^ 2 := by
    intro z hz
    rw [Complex.fderiv_det (hG z hz).differentiableAt, abs_of_nonneg (sq_nonneg _)]
  rw [setLIntegral_congr_fun measurableSet_ball (fun z hz ↦ by rw [hdet z hz])] at hcov
  rw [← hcov]
  calc
    (∫⁻ w : ℂ in G '' ball 0 1, outerTargetKernel w) ≤
        ∫⁻ w : ℂ, outerTargetKernel w := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (8 * Real.pi) := outerTargetKernel_lintegral

/-- Koebe's lower estimate makes the reciprocal image norm integrable on the disk. -/
lemma lintegral_inv_norm_comp_le {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hdG0 : deriv G 0 = 1) :
    (∫⁻ z : ℂ in ball 0 1, ENNReal.ofReal (1 / ‖G z‖)) ≤
      ENNReal.ofReal (8 * Real.pi) := by
  calc
    (∫⁻ z : ℂ in ball 0 1, ENNReal.ofReal (1 / ‖G z‖)) ≤
        ∫⁻ z : ℂ in ball 0 1, ENNReal.ofReal (4 * (1 / ‖z‖)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hzmem
      by_cases hz : z = 0
      · subst z
        simp [hG0]
      · have hlower := KoebeDistortion.norm_div_four_le_norm hG hinj hG0 hdG0 hzmem
        have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
        apply ENNReal.ofReal_le_ofReal
        calc
          1 / ‖G z‖ ≤ 1 / (‖z‖ / 4) :=
            one_div_le_one_div_of_le (div_pos hzpos (by norm_num : (0 : ℝ) < 4)) hlower
          _ = 4 * (1 / ‖z‖) := by field_simp
    _ = ENNReal.ofReal 4 *
        (∫⁻ z : ℂ in ball 0 1, ENNReal.ofReal (1 / ‖z‖)) := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (8 * Real.pi) := by
      rw [lintegral_ball_inv_norm]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring

lemma lintegral_one_sub_rpow_neg_half :
    (∫⁻ r : ℝ in Ioc 0 1, ENNReal.ofReal ((1 - r) ^ (-(1 : ℝ) / 2))) =
      ENNReal.ofReal 2 := by
  have hint : IntegrableOn (fun r : ℝ ↦ (1 - r) ^ (-(1 : ℝ) / 2)) (Ioc 0 1) := by
    have hbase : IntervalIntegrable (fun r : ℝ ↦ r ^ (-(1 : ℝ) / 2)) volume 0 1 := by
      exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hcomp := hbase.comp_sub_left (1 : ℝ)
    simpa only [sub_zero, sub_self] using hcomp.2
  have hnonneg : ∀ᵐ r ∂volume.restrict (Ioc (0 : ℝ) 1),
      0 ≤ (1 - r) ^ (-(1 : ℝ) / 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact Real.rpow_nonneg (sub_nonneg.mpr hr.2) _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  congr 1
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [intervalIntegral.integral_comp_sub_left (fun r : ℝ ↦ r ^ (-(1 : ℝ) / 2)) 1]
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num

/-- The crude, but explicit, polar integral used for the quarter-power source term. -/
lemma lintegral_ball_one_sub_norm_rpow_neg_half_le :
    (∫⁻ z : ℂ in ball 0 1,
      ENNReal.ofReal ((1 - ‖z‖) ^ (-(1 : ℝ) / 2))) ≤
      ENNReal.ofReal (4 * Real.pi) := by
  classical
  let f : ℂ → ℝ≥0∞ := (ball (0 : ℂ) 1).indicator
    (fun z ↦ ENNReal.ofReal ((1 - ‖z‖) ^ (-(1 : ℝ) / 2)))
  have hpolar := Complex.lintegral_comp_polarCoord_symm f
  rw [← lintegral_indicator measurableSet_ball]
  change (∫⁻ z : ℂ, f z) ≤ _
  rw [← hpolar, polarCoord_target]
  let T : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  let S : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi
  rw [← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  calc
    (∫⁻ p : ℝ × ℝ, T.indicator
        (fun p ↦ ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) p) ≤
        ∫⁻ p : ℝ × ℝ in S,
          ENNReal.ofReal ((1 - p.1) ^ (-(1 : ℝ) / 2)) := by
      rw [← lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
      apply lintegral_mono
      intro p
      by_cases hpT : p ∈ T
      · by_cases hr : p.1 < 1
        · have hpS : p ∈ S := ⟨⟨hpT.1, hr⟩, hpT.2⟩
          rw [Set.indicator_of_mem hpT, Set.indicator_of_mem hpS]
          have hp : 0 < p.1 := hpT.1
          have hnorm : ‖(Complex.polarCoord.symm p : ℂ)‖ = p.1 := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hp]
          have hball : (Complex.polarCoord.symm p : ℂ) ∈ ball 0 1 := by
            simpa only [mem_ball, dist_zero_right, hnorm] using hr
          dsimp [f]
          rw [Set.indicator_of_mem hball, hnorm]
          rw [← ENNReal.ofReal_mul hp.le]
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_of_le_one_left (Real.rpow_nonneg (sub_nonneg.mpr hr.le) _) hr.le
        · have hpS : p ∉ S := fun h ↦ hr h.1.2
          rw [Set.indicator_of_mem hpT, Set.indicator_of_notMem hpS]
          have hp : 0 < p.1 := hpT.1
          have hnorm : ‖(Complex.polarCoord.symm p : ℂ)‖ = p.1 := by
            rw [Complex.norm_polarCoord_symm, abs_of_pos hp]
          have hball : (Complex.polarCoord.symm p : ℂ) ∉ ball 0 1 := by
            simpa only [mem_ball, dist_zero_right, hnorm] using hr
          dsimp [f]
          rw [Set.indicator_of_notMem hball]
          simp
      · have hpS : p ∉ S := by
          intro h
          exact hpT ⟨h.1.1, h.2⟩
        rw [Set.indicator_of_notMem hpT, Set.indicator_of_notMem hpS]
    _ = ∫⁻ r : ℝ in Ioo 0 1,
        ENNReal.ofReal ((1 - r) ^ (-(1 : ℝ) / 2)) * volume (Ioo (-Real.pi) Real.pi) := by
      change (∫⁻ p : ℝ × ℝ in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal ((1 - p.1) ^ (-(1 : ℝ) / 2))) = _
      rw [Measure.volume_eq_prod, MeasureTheory.setLIntegral_prod]
      · apply lintegral_congr
        intro r
        change (∫⁻ _ : ℝ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal ((1 - r) ^ (-(1 : ℝ) / 2))) = _
        rw [MeasureTheory.setLIntegral_const]
      · fun_prop
    _ = ENNReal.ofReal (4 * Real.pi) := by
      rw [Real.volume_Ioo]
      rw [MeasureTheory.lintegral_mul_const _ (by fun_prop)]
      rw [setLIntegral_congr (Ioo_ae_eq_Ioc' (by simp : volume ({1} : Set ℝ) = 0))]
      rw [lintegral_one_sub_rpow_neg_half]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

lemma norm_comp_quarter_le_envelope {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1))
    (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hdG0 : deriv G 0 = 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖G z‖ ^ ((1 : ℝ) / 4) ≤ (1 - ‖z‖) ^ (-(1 : ℝ) / 2) := by
  let b : PrawitzProof.NormalizedUnivalent G :=
    PrawitzProof.NormalizedUnivalent.mk hG hinj hG0 hdG0
  have hg := b.norm_G_le_growth hz
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
  have hz1 : ‖z‖ < 1 := by simpa [Metric.mem_ball] using hz
  calc
    ‖G z‖ ^ ((1 : ℝ) / 4) ≤
        (‖z‖ / (1 - ‖z‖) ^ 2) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (norm_nonneg _) hg (by norm_num)
    _ = ‖z‖ ^ ((1 : ℝ) / 4) * (1 - ‖z‖) ^ (-(1 : ℝ) / 2) := by
      rw [Real.div_rpow hz0 (sq_nonneg _)]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ 1 - ‖z‖)]
      rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
      congr 1
      ring
    _ ≤ (1 - ‖z‖) ^ (-(1 : ℝ) / 2) := by
      apply mul_le_of_le_one_left (Real.rpow_nonneg (by linarith) _)
      exact Real.rpow_le_one (norm_nonneg _) (by linarith) (by norm_num)

/-- Koebe's upper estimate gives a uniform, explicit quarter-power area bound. -/
lemma lintegral_norm_comp_quarter_le {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1))
    (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hdG0 : deriv G 0 = 1) :
    (∫⁻ z : ℂ in ball 0 1, ENNReal.ofReal (‖G z‖ ^ ((1 : ℝ) / 4))) ≤
      ENNReal.ofReal (4 * Real.pi) := by
  calc
    (∫⁻ z : ℂ in ball 0 1, ENNReal.ofReal (‖G z‖ ^ ((1 : ℝ) / 4))) ≤
        ∫⁻ z : ℂ in ball 0 1,
          ENNReal.ofReal ((1 - ‖z‖) ^ (-(1 : ℝ) / 2)) := by
      apply setLIntegral_mono' measurableSet_ball
      intro z hz
      exact ENNReal.ofReal_le_ofReal (norm_comp_quarter_le_envelope hG hinj hG0 hdG0 hz)
    _ ≤ ENNReal.ofReal (4 * Real.pi) :=
      lintegral_ball_one_sub_norm_rpow_neg_half_le

private lemma young_small (a b : ℝ) (hb : 0 ≤ b) :
    a / b ≤ (1 / 2 : ℝ) * (a ^ 2 / b + 1 / b) := by
  by_cases hb0 : b = 0
  · simp [hb0]
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    rw [div_le_iff₀ hbpos]
    field_simp
    nlinarith [sq_nonneg (a - 1)]

private lemma young_large (a b : ℝ) (hb : 1 ≤ b) :
    a / b ≤ (1 / 2 : ℝ) *
      (a ^ 2 * b ^ (-(9 : ℝ) / 4) + b ^ ((1 : ℝ) / 4)) := by
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  let x := a / b ^ ((9 : ℝ) / 8)
  let y := b ^ ((1 : ℝ) / 8)
  have hamgm : 2 * x * y ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have hx : x * y = a / b := by
    dsimp [x, y]
    have hden : b ^ ((9 : ℝ) / 8) = b ^ ((1 : ℝ) / 8) * b := by
      calc
        b ^ ((9 : ℝ) / 8) = b ^ ((1 : ℝ) / 8 + 1) := by congr 1; ring
        _ = b ^ ((1 : ℝ) / 8) * b ^ (1 : ℝ) := Real.rpow_add hbpos _ _
        _ = b ^ ((1 : ℝ) / 8) * b := by rw [Real.rpow_one]
    rw [hden]
    field_simp [Real.rpow_pos_of_pos hbpos]
  have hx2 : x ^ 2 = a ^ 2 * b ^ (-(9 : ℝ) / 4) := by
    dsimp [x]
    rw [div_pow, ← Real.rpow_natCast (b ^ ((9 : ℝ) / 8)) 2,
      ← Real.rpow_mul hbpos.le]
    have hp : b ^ ((9 : ℝ) / 8 * (↑(2 : ℕ) : ℝ)) = b ^ ((9 : ℝ) / 4) := by
      congr 1
      norm_num
    rw [hp]
    have hneg : (-(9 : ℝ) / 4) = -((9 : ℝ) / 4) := by ring
    rw [hneg, Real.rpow_neg hbpos.le, div_eq_mul_inv]
  have hy2 : y ^ 2 = b ^ ((1 : ℝ) / 4) := by
    dsimp [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbpos.le]
    congr 1
    ring
  calc
    a / b = (1 / 2 : ℝ) * (2 * (a / b)) := by ring
    _ = (1 / 2 : ℝ) * (2 * x * y) := by rw [← hx]; ring
    _ ≤ (1 / 2 : ℝ) * (x ^ 2 + y ^ 2) :=
      mul_le_mul_of_nonneg_left hamgm (by norm_num)
    _ = (1 / 2 : ℝ) *
      (a ^ 2 * b ^ (-(9 : ℝ) / 4) + b ^ ((1 : ℝ) / 4)) := by rw [hx2, hy2]

/-- A four-term nonnegative majorant for the logarithmic derivative. -/
def logAreaMajorant (G : ℂ → ℂ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / 2) *
      (ENNReal.ofReal (‖deriv G z‖ ^ 2) * innerTargetKernel (G z) +
        ENNReal.ofReal (1 / ‖G z‖)) +
    ENNReal.ofReal (1 / 2) *
      (ENNReal.ofReal (‖deriv G z‖ ^ 2) * outerTargetKernel (G z) +
        ENNReal.ofReal (‖G z‖ ^ ((1 : ℝ) / 4)))

lemma logDerivative_le_logAreaMajorant (G : ℂ → ℂ) (z : ℂ) :
    ENNReal.ofReal (‖deriv G z‖ / ‖G z‖) ≤ logAreaMajorant G z := by
  let a := ‖deriv G z‖
  let b := ‖G z‖
  have hb : 0 ≤ b := norm_nonneg _
  by_cases hsmall : b < 1
  · have hmem : G z ∈ ball (0 : ℂ) 1 := by simpa [Metric.mem_ball, b]
    have hY : ENNReal.ofReal (a / b) ≤
        ENNReal.ofReal (1 / 2) *
          (ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (1 / b) + ENNReal.ofReal (1 / b)) := by
      calc
        ENNReal.ofReal (a / b) ≤
            ENNReal.ofReal ((1 / 2 : ℝ) * (a ^ 2 * (1 / b) + 1 / b)) := by
          apply ENNReal.ofReal_le_ofReal
          simpa [div_eq_mul_inv] using young_small a b hb
        _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          rw [ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (by positivity)) (by positivity)]
          rw [ENNReal.ofReal_mul (sq_nonneg a)]
    change ENNReal.ofReal (a / b) ≤ _
    change _ ≤ ENNReal.ofReal (1 / 2) *
      (ENNReal.ofReal (a ^ 2) * innerTargetKernel (G z) + ENNReal.ofReal (1 / b)) + _
    rw [innerTargetKernel, Set.indicator_of_mem hmem]
    exact hY.trans (self_le_add_right _ _)
  · have hlarge : 1 ≤ b := le_of_not_gt hsmall
    have hmem : G z ∈ {w : ℂ | 1 ≤ ‖w‖} := by simpa [b]
    have hY : ENNReal.ofReal (a / b) ≤
        ENNReal.ofReal (1 / 2) *
          (ENNReal.ofReal (a ^ 2) * ENNReal.ofReal (b ^ (-(9 : ℝ) / 4)) +
            ENNReal.ofReal (b ^ ((1 : ℝ) / 4))) := by
      calc
        ENNReal.ofReal (a / b) ≤ ENNReal.ofReal ((1 / 2 : ℝ) *
            (a ^ 2 * b ^ (-(9 : ℝ) / 4) + b ^ ((1 : ℝ) / 4))) := by
          exact ENNReal.ofReal_le_ofReal (young_large a b hlarge)
        _ = _ := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          rw [ENNReal.ofReal_add (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hb _))
            (Real.rpow_nonneg hb _)]
          rw [ENNReal.ofReal_mul (sq_nonneg a)]
    change ENNReal.ofReal (a / b) ≤ _
    change _ ≤ _ + ENNReal.ofReal (1 / 2) *
      (ENNReal.ofReal (a ^ 2) * outerTargetKernel (G z) +
        ENNReal.ofReal (b ^ ((1 : ℝ) / 4)))
    rw [outerTargetKernel, Set.indicator_of_mem hmem]
    exact hY.trans (le_add_left (by simpa [a, b]))

lemma measurable_innerTargetKernel : Measurable innerTargetKernel := by
  unfold innerTargetKernel
  apply Measurable.indicator
  · fun_prop
  · exact measurableSet_ball

lemma measurable_outerTargetKernel : Measurable outerTargetKernel := by
  unfold outerTargetKernel
  apply Measurable.indicator
  · fun_prop
  · exact measurableSet_le continuous_const.measurable continuous_norm.measurable

/-- The planar logarithmic derivative has total mass at most the fixed area constant. -/
lemma lintegral_logAreaMajorant_le {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1))
    (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hdG0 : deriv G 0 = 1) :
    (∫⁻ z : ℂ in ball 0 1, logAreaMajorant G z) ≤ ENNReal.ofReal logAreaConstant := by
  let μ := volume.restrict (ball (0 : ℂ) 1)
  have hGae : AEMeasurable G μ := hG.continuousOn.aemeasurable measurableSet_ball
  have hdGae : AEMeasurable (deriv G) μ :=
    hG.deriv.continuousOn.aemeasurable measurableSet_ball
  have hdsq : AEMeasurable (fun z ↦ ENNReal.ofReal (‖deriv G z‖ ^ 2)) μ :=
    (hdGae.norm.pow aemeasurable_const).ennreal_ofReal
  have hinner : AEMeasurable (fun z ↦ innerTargetKernel (G z)) μ := by
    simpa [Function.comp_def] using measurable_innerTargetKernel.comp_aemeasurable hGae
  have houter : AEMeasurable (fun z ↦ outerTargetKernel (G z)) μ := by
    simpa [Function.comp_def] using measurable_outerTargetKernel.comp_aemeasurable hGae
  have hinv : AEMeasurable (fun z ↦ ENNReal.ofReal (1 / ‖G z‖)) μ :=
    (hGae.norm.const_div 1).ennreal_ofReal
  have hquarter : AEMeasurable
      (fun z ↦ ENNReal.ofReal (‖G z‖ ^ ((1 : ℝ) / 4))) μ :=
    (hGae.norm.pow aemeasurable_const).ennreal_ofReal
  have hA := hdsq.mul hinner
  have hC := hdsq.mul houter
  change (∫⁻ z : ℂ, logAreaMajorant G z ∂μ) ≤ _
  have hEq : (∫⁻ z : ℂ, logAreaMajorant G z ∂μ) =
      ENNReal.ofReal (1 / 2) *
          ((∫⁻ z : ℂ, ENNReal.ofReal (‖deriv G z‖ ^ 2) * innerTargetKernel (G z) ∂μ) +
            (∫⁻ z : ℂ, ENNReal.ofReal (1 / ‖G z‖) ∂μ)) +
        ENNReal.ofReal (1 / 2) *
          ((∫⁻ z : ℂ, ENNReal.ofReal (‖deriv G z‖ ^ 2) * outerTargetKernel (G z) ∂μ) +
            (∫⁻ z : ℂ, ENNReal.ofReal (‖G z‖ ^ ((1 : ℝ) / 4)) ∂μ)) := by
    let A : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖deriv G z‖ ^ 2) * innerTargetKernel (G z)
    let B : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (1 / ‖G z‖)
    let C : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖deriv G z‖ ^ 2) * outerTargetKernel (G z)
    let D : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖G z‖ ^ ((1 : ℝ) / 4))
    have hA' : AEMeasurable A μ := hA
    have hB' : AEMeasurable B μ := hinv
    have hC' : AEMeasurable C μ := hC
    have hD' : AEMeasurable D μ := hquarter
    have hAB : (∫⁻ z, A z + B z ∂μ) = (∫⁻ z, A z ∂μ) + ∫⁻ z, B z ∂μ := by
      simpa only [Pi.add_apply] using lintegral_add_left' hA' B
    have hCD : (∫⁻ z, C z + D z ∂μ) = (∫⁻ z, C z ∂μ) + ∫⁻ z, D z ∂μ := by
      simpa only [Pi.add_apply] using lintegral_add_left' hC' D
    have hhalfAB : (∫⁻ z, ENNReal.ofReal (1 / 2) * (A z + B z) ∂μ) =
        ENNReal.ofReal (1 / 2) * ∫⁻ z, A z + B z ∂μ :=
      lintegral_const_mul'' _ (hA'.add hB')
    have hhalfCD : (∫⁻ z, ENNReal.ofReal (1 / 2) * (C z + D z) ∂μ) =
        ENNReal.ofReal (1 / 2) * ∫⁻ z, C z + D z ∂μ :=
      lintegral_const_mul'' _ (hC'.add hD')
    unfold logAreaMajorant
    change (∫⁻ z, ENNReal.ofReal (1 / 2) * (A z + B z) +
      ENNReal.ofReal (1 / 2) * (C z + D z) ∂μ) = _
    rw [show (∫⁻ z, ENNReal.ofReal (1 / 2) * (A z + B z) +
        ENNReal.ofReal (1 / 2) * (C z + D z) ∂μ) =
      (∫⁻ z, ENNReal.ofReal (1 / 2) * (A z + B z) ∂μ) +
        (∫⁻ z, ENNReal.ofReal (1 / 2) * (C z + D z) ∂μ) by
      simpa only [Pi.add_apply, Pi.mul_apply] using
        lintegral_add_left' (aemeasurable_const.mul (hA'.add hB'))
          (fun z ↦ ENNReal.ofReal (1 / 2) * (C z + D z))]
    rw [hhalfAB, hhalfCD, hAB, hCD]
  rw [hEq]
  have hAi := lintegral_jacobian_inner_le hG hinj
  have hBi := lintegral_inv_norm_comp_le hG hinj hG0 hdG0
  have hCi := lintegral_jacobian_outer_le hG hinj
  have hDi := lintegral_norm_comp_quarter_le hG hinj hG0 hdG0
  calc
    _ ≤ ENNReal.ofReal (1 / 2) *
          (ENNReal.ofReal (2 * Real.pi) + ENNReal.ofReal (8 * Real.pi)) +
        ENNReal.ofReal (1 / 2) *
          (ENNReal.ofReal (8 * Real.pi) + ENNReal.ofReal (4 * Real.pi)) := by gcongr
    _ ≤ ENNReal.ofReal logAreaConstant := by
      unfold logAreaConstant
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * Real.pi)
        (by positivity : 0 ≤ 8 * Real.pi)]
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 8 * Real.pi)
        (by positivity : 0 ≤ 4 * Real.pi)]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])

/-- Polar/Fubini identification of the angular radial integral with planar logarithmic area. -/
lemma angular_lintegral_logRadialIntegralE_eq {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) :
    (∫⁻ θ in angleDomain, logRadialIntegralE G θ) =
      ∫⁻ z : ℂ in ball 0 1, ENNReal.ofReal (‖deriv G z‖ / ‖G z‖) := by
  have hGsub : Measurable (fun z : ball (0 : ℂ) 1 ↦ G z) :=
    hG.continuousOn.domRestrict.measurable
  have hdGsub : Measurable (fun z : ball (0 : ℂ) 1 ↦ deriv G z) :=
    hG.deriv.continuousOn.domRestrict.measurable
  let emb : ball (0 : ℂ) 1 → ℂ := Subtype.val
  have hemb : MeasurableEmbedding emb := MeasurableEmbedding.subtype_coe measurableSet_ball
  obtain ⟨Gm, hGm, hGm_eq⟩ := hemb.exists_measurable_extend hGsub (fun _ ↦ ⟨0⟩)
  obtain ⟨Dm, hDm, hDm_eq⟩ := hemb.exists_measurable_extend hdGsub (fun _ ↦ ⟨0⟩)
  let q : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖Dm z‖ / ‖Gm z‖)
  have hq : Measurable q := by
    dsimp [q]
    exact (hDm.norm.div hGm.norm).ennreal_ofReal
  have hqeq : ∀ z ∈ ball (0 : ℂ) 1,
      q z = ENNReal.ofReal (‖deriv G z‖ / ‖G z‖) := by
    intro z hz
    have hGe := congrFun hGm_eq ⟨z, hz⟩
    have hDe := congrFun hDm_eq ⟨z, hz⟩
    change Gm z = G z at hGe
    change Dm z = deriv G z at hDe
    change ENNReal.ofReal (‖Dm z‖ / ‖Gm z‖) = _
    rw [hGe, hDe]
  have hplanar : (∫⁻ z : ℂ in ball 0 1, q z) =
      ∫⁻ z : ℂ in ball 0 1, ENNReal.ofReal (‖deriv G z‖ / ‖G z‖) := by
    exact setLIntegral_congr_fun measurableSet_ball hqeq
  have hray : ∀ θ : ℝ,
      (∫⁻ r in Ioc (0 : ℝ) 1, ENNReal.ofReal r * q (circlePoint r θ)) =
        logRadialIntegralE G θ := by
    intro θ
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    unfold logRadialIntegralE
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have hz : circlePoint r θ ∈ ball (0 : ℂ) 1 := by
      simp only [circlePoint, mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr.1, Complex.norm_exp, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
        zero_mul, sub_zero, Real.exp_zero, mul_one]
      exact hr.2
    change ENNReal.ofReal r * q (circlePoint r θ) =
      ENNReal.ofReal (r * ‖deriv G (circlePoint r θ)‖ / ‖G (circlePoint r θ)‖)
    rw [hqeq _ hz]
    rw [← ENNReal.ofReal_mul hr.1.le]
    congr 1
    ring
  rw [← hplanar, lintegral_ball_eq_polar q hq]
  unfold angleDomain
  rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro θ _
  exact (hray θ).symm

/-- The total angular logarithmic-derivative integral is uniformly bounded. -/
lemma angular_lintegral_logRadialIntegralE_le {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1))
    (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hdG0 : deriv G 0 = 1) :
    (∫⁻ θ in angleDomain, logRadialIntegralE G θ) ≤
      ENNReal.ofReal logAreaConstant := by
  rw [angular_lintegral_logRadialIntegralE_eq hG]
  exact (setLIntegral_mono' measurableSet_ball
    (fun z _ ↦ logDerivative_le_logAreaMajorant G z)).trans
      (lintegral_logAreaMajorant_le hG hinj hG0 hdG0)

/-- The radial logarithmic-derivative integral is measurable as a function of direction. -/
lemma measurable_logRadialIntegralE {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) :
    Measurable (logRadialIntegralE G) := by
  have hGsub : Measurable (fun z : ball (0 : ℂ) 1 ↦ G z) :=
    hG.continuousOn.domRestrict.measurable
  have hdGsub : Measurable (fun z : ball (0 : ℂ) 1 ↦ deriv G z) :=
    hG.deriv.continuousOn.domRestrict.measurable
  let emb : ball (0 : ℂ) 1 → ℂ := Subtype.val
  have hemb : MeasurableEmbedding emb := MeasurableEmbedding.subtype_coe measurableSet_ball
  obtain ⟨Gm, hGm, hGm_eq⟩ := hemb.exists_measurable_extend hGsub (fun _ ↦ ⟨0⟩)
  obtain ⟨Dm, hDm, hDm_eq⟩ := hemb.exists_measurable_extend hdGsub (fun _ ↦ ⟨0⟩)
  let q : ℂ → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖Dm z‖ / ‖Gm z‖)
  have hq : Measurable q := by
    dsimp [q]
    exact (hDm.norm.div hGm.norm).ennreal_ofReal
  have hqeq : ∀ z ∈ ball (0 : ℂ) 1,
      q z = ENNReal.ofReal (‖deriv G z‖ / ‖G z‖) := by
    intro z hz
    have hGe := congrFun hGm_eq ⟨z, hz⟩
    have hDe := congrFun hDm_eq ⟨z, hz⟩
    change Gm z = G z at hGe
    change Dm z = deriv G z at hDe
    change ENNReal.ofReal (‖Dm z‖ / ‖Gm z‖) = _
    rw [hGe, hDe]
  let H : ℝ → ℝ≥0∞ := fun θ ↦
    ∫⁻ r in Ioc (0 : ℝ) 1,
      ENNReal.ofReal r * q (circlePoint r θ)
  have hjoint : Measurable (Function.uncurry fun θ r ↦
      ENNReal.ofReal r * q (circlePoint r θ)) := by
    change Measurable (fun p : ℝ × ℝ ↦
      ENNReal.ofReal p.2 * q (circlePoint p.2 p.1))
    have hcircle : Measurable (fun p : ℝ × ℝ ↦ circlePoint p.2 p.1) := by
      unfold circlePoint
      fun_prop
    exact (ENNReal.continuous_ofReal.measurable.comp measurable_snd).mul (hq.comp hcircle)
  have hH : Measurable H := hjoint.lintegral_prod_right
  have hHeq : H = logRadialIntegralE G := by
    funext θ
    dsimp only [H]
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    unfold logRadialIntegralE
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have hz : circlePoint r θ ∈ ball (0 : ℂ) 1 := by
      simp only [circlePoint, mem_ball, dist_zero_right, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr.1, Complex.norm_exp, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
        zero_mul, sub_zero, Real.exp_zero, mul_one]
      exact hr.2
    change ENNReal.ofReal r * q (circlePoint r θ) =
      ENNReal.ofReal (r * ‖deriv G (circlePoint r θ)‖ / ‖G (circlePoint r θ)‖)
    rw [hqeq _ hz]
    rw [← ENNReal.ofReal_mul hr.1.le]
    congr 1
    ring
  rw [← hHeq]
  exact hH

/-- The explicit logarithmic exceptional set has angular measure strictly below `π/4`. -/
theorem volume_logBad_lt_quarter {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1))
    (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hdG0 : deriv G 0 = 1) :
    volume (logBad G) < ENNReal.ofReal (Real.pi / 4) := by
  have hmeas : Measurable (logRadialIntegralE G) := measurable_logRadialIntegralE hG
  have hbadmeas : MeasurableSet (logBad G) := by
    unfold logBad
    exact measurableSet_Ico.inter (measurableSet_lt measurable_const hmeas)
  have hbadsub : logBad G ⊆ angleDomain := by
    intro θ hθ
    exact hθ.1
  have hlarge : logBad G ⊆
      {θ | ENNReal.ofReal logThreshold ≤ logRadialIntegralE G θ} := by
    intro θ hθ
    exact hθ.2.le
  have hbound : volume (logBad G) ≤
      ENNReal.ofReal logAreaConstant / ENNReal.ofReal logThreshold := by
    exact innerRadialMax_projection_bound hbadmeas hbadsub
      hmeas.aemeasurable hlarge
      (ENNReal.ofReal_ne_zero_iff.mpr logThreshold_pos)
      ENNReal.ofReal_ne_top
      (angular_lintegral_logRadialIntegralE_le hG hinj hG0 hdG0)
  refine hbound.trans_lt ?_
  rw [← ENNReal.ofReal_div_of_pos logThreshold_pos]
  exact ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < Real.pi / 4) |>.2 (by
    unfold logThreshold
    have hA := logAreaConstant_pos
    have hpi := Real.pi_pos
    field_simp
    nlinarith)

/-- Outside the logarithmic exceptional set, any radial-maximal bound `K` combines with the
fixed logarithmic threshold to bound the variation of the radial image curve. -/
theorem normalized_radialCurve_eVariation_le_of_not_mem_logBad
    {G : ℂ → ℂ} {theta K : ℝ}
    (hG : AnalyticOnNhd ℂ G (ball 0 1)) (hinj : InjOn G (ball 0 1))
    (hG0 : G 0 = 0) (hK : 0 ≤ K)
    (htheta : theta ∈ angleDomain) (hbad : theta ∉ logBad G)
    (hquot : ∀ r ∈ Ioo (0 : ℝ) 1, radialQuotient G r theta ≤ K) :
    eVariationOn (shortPathRadialCurve G theta) (Ico (0 : ℝ) 1) ≤
      ENNReal.ofReal (K * logThreshold) := by
  exact RadialVariation.normalized_radialCurve_eVariation_le hG hinj hG0
    hK logThreshold_nonneg hquot
      (logRadialIntegralE_le_of_not_mem_logBad htheta hbad)

end LogDerivative
end Erdos515
