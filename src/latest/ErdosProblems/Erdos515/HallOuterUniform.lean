/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.HallRadialSup

/-!
# A uniform bound for Hall's outer slit potential

This file turns the pointwise self-radius/Poisson estimates into the uniform finite-family
estimate needed by the outer half of Hall's lemma.
-/

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Topology BigOperators

namespace Erdos515

lemma intervalIntegral_outerPoissonMajorant {z : ℂ} (hz : ‖z‖ < 1) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), outerPoissonMajorant z θ = 2 * Real.pi := by
  have hformula :=
    (InnerProductSpace.harmonicOnNhd_const (1 : ℝ)).circleAverage_poissonKernel_smul
      (c := (0 : ℂ)) (R := (1 : ℝ)) (w := z) (by simpa [Metric.mem_ball] using hz)
  rw [Real.circleAverage_def] at hformula
  simp only [smul_eq_mul, Pi.mul_apply, mul_one] at hformula
  have hmap : (fun θ : ℝ ↦ poissonKernel 0 z (circleMap 0 1 θ)) =
      (fun θ : ℝ ↦ outerPoissonMajorant z θ) := by
    funext θ
    simp [outerPoissonMajorant, circleMap, radialPoint]
  rw [hmap] at hformula
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), outerPoissonMajorant z θ) =
        (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), outerPoissonMajorant z θ) := by
      field_simp [Real.pi_ne_zero]
    _ = 2 * Real.pi := by rw [hformula]; norm_num

lemma integrable_outerPoissonMajorant {z : ℂ} (hz : ‖z‖ < 1) :
    Integrable (outerPoissonMajorant z) (volume.restrict angleDomain) := by
  have hcont : Continuous (outerPoissonMajorant z) := by
    unfold outerPoissonMajorant poissonKernel radialPoint
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro θ hzero
      have hnorm : ‖((1 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - z‖ = 0 := by
        exact sq_eq_zero_iff.mp (by simpa using hzero)
      have heq : ((1 : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = z :=
        sub_eq_zero.mp (norm_eq_zero.mp hnorm)
      have := congrArg norm heq
      simp at this
      linarith
  have hI : IntervalIntegrable (outerPoissonMajorant z) volume 0 (2 * Real.pi) :=
    hcont.intervalIntegrable _ _
  rw [angleDomain]
  exact (intervalIntegrable_iff_integrableOn_Ico_of_le (by positivity)).1 hI

lemma lintegral_outerPoissonMajorant {z : ℂ} (hz : ‖z‖ < 1) :
    ∫⁻ θ in angleDomain, ENNReal.ofReal (outerPoissonMajorant z θ) =
      ENNReal.ofReal (2 * Real.pi) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_outerPoissonMajorant hz)
    (ae_of_all _ (outerPoissonMajorant_nonneg hz))]
  rw [angleDomain, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity)]
  exact congrArg ENNReal.ofReal (intervalIntegral_outerPoissonMajorant hz)

lemma measurable_outerSelfGreen (z : ℂ) : Measurable (outerSelfGreen z) := by
  unfold outerSelfGreen
  apply Measurable.div_const
  exact (measurable_diskGreenENNReal_right z).comp (by
    unfold radialPoint
    fun_prop)

lemma measurable_outerPoissonMajorant (z : ℂ) : Measurable (outerPoissonMajorant z) := by
  unfold outerPoissonMajorant poissonKernel radialPoint
  fun_prop

/-- The common majorant for logarithmically normalized outer Green kernels has a uniform
angular integral.  The deliberately generous constant `128 * π` also covers poles near the
origin, where the pointwise bound is the constant `64`. -/
theorem lintegral_outerNormalizedGreenMajorant {z : ℂ} (hz : ‖z‖ < 1) :
    ∫⁻ θ in angleDomain, outerNormalizedGreenMajorant z θ ≤
      ENNReal.ofReal (128 * Real.pi) := by
  by_cases hzsmall : ‖z‖ ≤ 1 / 8
  · simp only [outerNormalizedGreenMajorant, if_pos hzsmall]
    rw [MeasureTheory.setLIntegral_const, volume_angleDomain]
    rw [← ENNReal.ofReal_ofNat 64,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])
  · have hz0 : z ≠ 0 := by
      intro h
      subst z
      simp at hzsmall
    simp only [outerNormalizedGreenMajorant, if_neg hzsmall]
    have hself : Measurable (fun θ ↦ (16 : ℝ≥0∞) * outerSelfGreen z θ) :=
      measurable_const.mul (measurable_outerSelfGreen z)
    have hpoisson : Measurable
        (fun θ ↦ (16 : ℝ≥0∞) * ENNReal.ofReal (outerPoissonMajorant z θ)) :=
      measurable_const.mul
        (ENNReal.continuous_ofReal.measurable.comp (measurable_outerPoissonMajorant z))
    have hpullPoisson :
        (∫⁻ θ in angleDomain,
            (16 : ℝ≥0∞) * ENNReal.ofReal (outerPoissonMajorant z θ)) =
          16 * (∫⁻ θ in angleDomain, ENNReal.ofReal (outerPoissonMajorant z θ)) := by
      exact MeasureTheory.lintegral_const_mul (16 : ℝ≥0∞)
        (ENNReal.continuous_ofReal.measurable.comp (measurable_outerPoissonMajorant z))
    have hselfIntegral :
        (∫⁻ θ in angleDomain, outerSelfGreen z θ) =
          ENNReal.ofReal (2 * Real.pi) := by
      simpa [outerSelfGreen] using
        (lintegral_diskGreenENNReal_selfRadius_normalized hz0 hz)
    rw [MeasureTheory.lintegral_add_left hself,
      MeasureTheory.lintegral_const_mul _ (measurable_outerSelfGreen z),
      hpullPoisson,
      hselfIntegral,
      lintegral_outerPoissonMajorant hz]
    have hmul :
        (16 : ℝ≥0∞) * ENNReal.ofReal (2 * Real.pi) =
          ENNReal.ofReal (16 * (2 * Real.pi)) := by
      rw [← ENNReal.ofReal_ofNat 16,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
    rw [hmul, ← ENNReal.ofReal_add
      (by nlinarith [Real.pi_pos] : (0 : ℝ) ≤ 16 * (2 * Real.pi))
      (by nlinarith [Real.pi_pos] : (0 : ℝ) ≤ 16 * (2 * Real.pi))]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])

lemma greenPotential_logWeightedMeasure_le_outer
    (a : CircularArc) {z : ℂ} (hz : ‖z‖ < 1)
    (hr : (1 / 4 : ℝ) ≤ a.radius) :
    greenPotential a.logWeightedMeasure z ≤
      ∫⁻ θ in a.angles, outerNormalizedGreenMajorant z θ := by
  have hL := a.log_one_div_pos
  rw [greenPotential, CircularArc.logWeightedMeasure,
    MeasureTheory.lintegral_smul_measure]
  change ENNReal.ofReal (1 / Real.log (1 / a.radius)) *
      (∫⁻ ζ, diskGreenENNReal z ζ ∂Measure.map
        (fun θ ↦ radialPoint a.radius θ) (volume.restrict a.angles)) ≤ _
  rw [MeasureTheory.lintegral_map (measurable_diskGreenENNReal_right z)]
  · have hradmeas : Measurable (fun θ ↦ radialPoint a.radius θ) := by
      unfold radialPoint
      fun_prop
    have hkernel : Measurable
        (fun θ ↦ diskGreenENNReal z (radialPoint a.radius θ)) :=
      (measurable_diskGreenENNReal_right z).comp hradmeas
    calc
      ENNReal.ofReal (1 / Real.log (1 / a.radius)) *
          (∫⁻ θ in a.angles, diskGreenENNReal z (radialPoint a.radius θ)) =
          ∫⁻ θ in a.angles, ENNReal.ofReal (1 / Real.log (1 / a.radius)) *
            diskGreenENNReal z (radialPoint a.radius θ) := by
        exact (MeasureTheory.lintegral_const_mul _ hkernel).symm
      _ = ∫⁻ θ in a.angles, diskGreenENNReal z (radialPoint a.radius θ) /
          ENNReal.ofReal (Real.log (1 / a.radius)) := by
        apply lintegral_congr
        intro θ
        have hc : ENNReal.ofReal (1 / Real.log (1 / a.radius)) =
            1 / ENNReal.ofReal (Real.log (1 / a.radius)) := by
          simpa using ENNReal.ofReal_div_of_pos (x := 1) hL
        rw [hc]
        simp [div_eq_mul_inv, mul_comm]
      _ ≤ ∫⁻ θ in a.angles, outerNormalizedGreenMajorant z θ := by
        apply lintegral_mono
        intro θ
        exact diskGreenENNReal_div_log_le_outerNormalizedGreenMajorant
          hz hr a.radius_lt_one
  · unfold radialPoint
    fun_prop

/-- A finite family of outer slits with pairwise disjoint angular projections has uniformly
bounded logarithmically normalized Green potential. -/
theorem greenPotential_logMeasure_le_outer
    (A : DisjointRadialArcs) {z : ℂ} (hz : ‖z‖ < 1)
    (hr : ∀ i, (1 / 4 : ℝ) ≤ (A.arc i).radius)
    (hangle : A.angularSupport ⊆ angleDomain) :
    greenPotential A.logMeasure z ≤ ENNReal.ofReal (128 * Real.pi) := by
  rw [greenPotential, DisjointRadialArcs.logMeasure,
    MeasureTheory.lintegral_finsetSum_measure]
  change (∑ i, greenPotential (A.arc i).logWeightedMeasure z) ≤ _
  calc
    (∑ i, greenPotential (A.arc i).logWeightedMeasure z) ≤
        ∑ i, ∫⁻ θ in (A.arc i).angles, outerNormalizedGreenMajorant z θ := by
      exact Finset.sum_le_sum fun i _ ↦
        greenPotential_logWeightedMeasure_le_outer (A.arc i) hz (hr i)
    _ = ∫⁻ θ in A.angularSupport, outerNormalizedGreenMajorant z θ := by
      rw [DisjointRadialArcs.angularSupport,
        MeasureTheory.lintegral_iUnion
          (fun i ↦ (A.arc i).measurableSet_angles)
          (fun i j hij ↦ A.angle_disjoint (Set.mem_univ i) (Set.mem_univ j) hij),
        tsum_fintype]
    _ ≤ ∫⁻ θ in angleDomain, outerNormalizedGreenMajorant z θ :=
      MeasureTheory.lintegral_mono_set hangle
    _ ≤ ENNReal.ofReal (128 * Real.pi) := lintegral_outerNormalizedGreenMajorant hz

end Erdos515
