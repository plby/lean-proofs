import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupOuterMeridianPaths
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspOuterCircleTrig
import Mathlib.Algebra.Ring.Periodic

/-!
# The actual clockwise outer circle and its slit bounds

The radius-two circle starts at `1/2 - 2i` and turns clockwise. Its periodic
real parametrization restricts to the reversal of the existing positive
outer circle. The shorter mapping-torus arcs lie in the actual slit planes.
-/

noncomputable section

open Set Complex
open scoped Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp

open SpecialPeriods.Triangle

/-- The genuine clockwise radius-two outer loop, based at its bottom point. -/
def outerClockwiseCircle :
    Path (outerCircleBasepoint (2 : ℝ) (by norm_num))
      (outerCircleBasepoint (2 : ℝ) (by norm_num)) :=
  (outerPositiveCircle (2 : ℝ) (by norm_num)).symm

/-- Its actual periodic parametrization on the whole real line. -/
def outerClockwiseCurve : C(ℝ, TwicePuncturedPlane) :=
  ⟨fun t => ⟨outerCircleValue 2 (-t),
      outerCircleValue_avoids_punctures 2 (by norm_num) (-t)⟩,
    ((continuous_outerCircleValue 2).comp continuous_neg).subtype_mk _⟩

@[simp] theorem outerClockwiseCurve_coe (t : ℝ) :
    (outerClockwiseCurve t : ℂ) = outerCircleValue 2 (-t) := rfl

private theorem outerValue_periodic (R : ℝ) : Function.Periodic (outerCircleValue R) 1 := by
  intro t
  unfold outerCircleValue
  rw [show -Real.pi / 2 + 2 * Real.pi * (t + 1) =
    (-Real.pi / 2 + 2 * Real.pi * t) + 2 * Real.pi by ring]
  exact periodic_circleMap (1 / 2 : ℂ) R _

/-- One complete clockwise turn has exactly the same value in the punctured plane. -/
theorem outerClockwiseCurve_periodic : Function.Periodic outerClockwiseCurve 1 := by
  intro t
  apply Subtype.ext
  change outerCircleValue 2 (-(t + 1)) = outerCircleValue 2 (-t)
  rw [show -(t + 1) = -t - 1 by ring]
  exact (outerValue_periodic 2).sub_eq (-t)

theorem outerClockwiseCurve_add_one (t : ℝ) :
    outerClockwiseCurve (t + 1) = outerClockwiseCurve t := outerClockwiseCurve_periodic t

theorem outerClockwiseCurve_add_int (t : ℝ) (k : ℤ) :
    outerClockwiseCurve (t + (k : ℝ)) = outerClockwiseCurve t := by
  simpa only [mul_one] using outerClockwiseCurve_periodic.int_mul k t

/-- On the unit interval this is literally the reversed positive outer circle. -/
theorem outerClockwiseCurve_unit (t : unitInterval) :
    outerClockwiseCurve (t : ℝ) = outerClockwiseCircle t := by
  apply Subtype.ext
  change outerCircleValue 2 (-(t : ℝ)) =
    outerCircleValue 2 ((unitInterval.symm t : unitInterval) : ℝ)
  rw [unitInterval.coe_symm_eq]
  exact (outerValue_periodic 2).sub_eq'.symm

@[simp] theorem outerClockwiseCurve_zero :
    (outerClockwiseCurve 0 : ℂ) = (1 / 2 : ℂ) - 2 * I := by
  simp only [outerClockwiseCurve_coe, neg_zero, outerCircleValue_zero, Complex.ofReal_ofNat]

theorem outerClockwiseCurve_zero_basepoint :
    outerClockwiseCurve 0 = outerCircleBasepoint (2 : ℝ) (by norm_num) :=
  Subtype.ext outerClockwiseCurve_zero

@[simp] theorem outerClockwiseCurve_one : outerClockwiseCurve 1 = outerClockwiseCurve 0 := by
  simpa only [zero_add] using outerClockwiseCurve_add_one 0

/-- Clockwise travel reaches the leftmost point at one quarter. -/
theorem outerClockwiseCurve_quarter :
    (outerClockwiseCurve (1 / 4) : ℂ) = -(3 / 2 : ℂ) := by
  rw [outerClockwiseCurve_coe]
  have h : outerCircleValue 2 (-(1 / 4 : ℝ)) = outerCircleValue 2 (3 / 4) := by
    convert ((outerValue_periodic 2) (-(1 / 4 : ℝ))).symm using 1
    norm_num
  rw [h, outerCircleValue_threeQuarters]
  norm_num

/-- Clockwise travel reaches the rightmost point at three quarters. -/
theorem outerClockwiseCurve_threeQuarters :
    (outerClockwiseCurve (3 / 4) : ℂ) = (5 / 2 : ℂ) := by
  rw [outerClockwiseCurve_coe]
  have h : outerCircleValue 2 (-(3 / 4 : ℝ)) = outerCircleValue 2 (1 / 4) := by
    convert ((outerValue_periodic 2) (-(3 / 4 : ℝ))).symm using 1
    norm_num
  rw [h, outerCircleValue_quarter]
  norm_num

/-- The real coordinate fixes the left-to-right order of the clockwise overlaps. -/
theorem outerClockwiseCurve_re (t : ℝ) :
    (outerClockwiseCurve t : ℂ).re = 1 / 2 - 2 * Real.sin (2 * Real.pi * t) := by
  have h := congrArg Complex.re
    (circleMap_sub_center (1 / 2 : ℂ) 2 (-Real.pi / 2 + 2 * Real.pi * (-t)))
  rw [Complex.sub_re, circleMap_zero_re,
    show -Real.pi / 2 + 2 * Real.pi * (-t) = -(2 * Real.pi * t) - Real.pi / 2 by ring,
    Real.cos_sub_pi_div_two, Real.sin_neg] at h
  norm_num at h
  change (circleMap (1 / 2 : ℂ) 2 (-Real.pi / 2 + 2 * Real.pi * (-t))).re = _
  rw [show -Real.pi / 2 + 2 * Real.pi * (-t) = -(2 * Real.pi * t) - Real.pi / 2 by ring]
  linarith

theorem outerClockwiseCurve_im (t : ℝ) :
    (outerClockwiseCurve t : ℂ).im = -2 * Real.cos (2 * Real.pi * t) := by
  rw [outerClockwiseCurve_coe, outerCircleValue_im,
    show -Real.pi / 2 + 2 * Real.pi * (-t) = -(2 * Real.pi * t) - Real.pi / 2 by ring,
    Real.sin_sub_pi_div_two, Real.cos_neg]
  ring

/-- The closed middle half of the reversed path lies in the upper slit plane. -/
theorem outerClockwiseCircle_mem_upperSlitPlane (t : unitInterval)
    (ht0 : 1 / 4 ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 3 / 4) :
    (outerClockwiseCircle t : ℂ) ∈ upperSlitPlane := by
  change (outerPositiveCircle 2 (by norm_num) (unitInterval.symm t) : ℂ) ∈ upperSlitPlane
  apply outerPositiveCircle_mem_upperSlitPlane
  · rw [unitInterval.coe_symm_eq]
    linarith
  · rw [unitInterval.coe_symm_eq]
    linarith

/-- The two closed end quarters of the reversed path lie in the lower slit plane. -/
theorem outerClockwiseCircle_mem_lowerSlitPlane (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (t : ℝ)) :
    (outerClockwiseCircle t : ℂ) ∈ lowerSlitPlane := by
  change (outerPositiveCircle 2 (by norm_num) (unitInterval.symm t) : ℂ) ∈ lowerSlitPlane
  apply outerPositiveCircle_mem_lowerSlitPlane
  rw [unitInterval.coe_symm_eq]
  rcases ht with ht | ht
  · exact Or.inr (by linarith)
  · exact Or.inl (by linarith)

/-- The full shortened first arc lies in the actual upper slit plane. -/
theorem outerClockwiseCurve_mem_upperSlitPlane (t : ℝ)
    (ht0 : 1 / 8 < t) (ht1 : t < 7 / 8) :
    (outerClockwiseCurve t : ℂ) ∈ upperSlitPlane := by
  by_cases hleft : t < 1 / 4
  · have hs := sin_two_pi_gt_half t ht0 (by linarith)
    apply Or.inr
    rw [outerClockwiseCurve_re]
    constructor <;> linarith
  by_cases hright : 3 / 4 < t
  · have hs := sin_two_pi_lt_neg_half (t - 1) (by linarith) (by linarith)
    rw [show 2 * Real.pi * (t - 1) = 2 * Real.pi * t - 2 * Real.pi by ring,
      Real.sin_sub_two_pi] at hs
    apply Or.inr
    rw [outerClockwiseCurve_re]
    constructor <;> linarith
  · let u : unitInterval := ⟨t, by constructor <;> linarith⟩
    change (outerClockwiseCurve (u : ℝ) : ℂ) ∈ upperSlitPlane
    rw [outerClockwiseCurve_unit]
    exact outerClockwiseCircle_mem_upperSlitPlane u
      (le_of_not_gt hleft) (le_of_not_gt hright)

/-- The full shortened arc crossing time zero lies in the actual lower slit plane. -/
theorem outerClockwiseCurve_mem_lowerSlitPlane (t : ℝ)
    (ht0 : -(3 / 8) < t) (ht1 : t < 3 / 8) :
    (outerClockwiseCurve t : ℂ) ∈ lowerSlitPlane := by
  by_cases hleft : t < -(1 / 4)
  · have hs := sin_two_pi_lt_neg_half t ht0 (by linarith)
    apply Or.inr
    rw [outerClockwiseCurve_re]
    constructor <;> linarith
  by_cases hright : 1 / 4 < t
  · have hs := sin_two_pi_gt_half t (by linarith) ht1
    apply Or.inr
    rw [outerClockwiseCurve_re]
    constructor <;> linarith
  by_cases hneg : t < 0
  · let u : unitInterval := ⟨t + 1, by constructor <;> linarith⟩
    have hu : 3 / 4 ≤ (u : ℝ) := by
      change 3 / 4 ≤ t + 1
      linarith
    have h := outerClockwiseCircle_mem_lowerSlitPlane u (Or.inr hu)
    rw [← outerClockwiseCurve_unit] at h
    change (outerClockwiseCurve (t + 1) : ℂ) ∈ lowerSlitPlane at h
    rwa [outerClockwiseCurve_add_one] at h
  · let u : unitInterval := ⟨t, by constructor <;> linarith⟩
    change (outerClockwiseCurve (u : ℝ) : ℂ) ∈ lowerSlitPlane
    rw [outerClockwiseCurve_unit]
    exact outerClockwiseCircle_mem_lowerSlitPlane u (Or.inl (le_of_not_gt hright))

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.Cusp
