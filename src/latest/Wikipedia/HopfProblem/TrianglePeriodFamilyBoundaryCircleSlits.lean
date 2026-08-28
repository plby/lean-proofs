import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryRadiusCore
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCircleSlitsTrig
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCover
import Mathlib.Algebra.Ring.Periodic

/-!
# Phased positive boundary circles in the actual slit cover

The zero-puncture circle starts at phase three quarters and the
one-puncture circle at phase one quarter. Both start below their puncture
and turn positively. Their quarter-time points have the literal real
coordinates fixing the two overlap components used by the mapping-torus
cover. No homology or attaching-map identification is assumed here.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryCircleSlits

open SpecialPeriods.Triangle BoundaryRadius

/-- The phase puts the starting point below the selected puncture. -/
def circlePhase : Bool → ℝ
  | false => 3 / 4
  | true => 1 / 4

@[simp] theorem circlePhase_false : circlePhase false = 3 / 4 := rfl

@[simp] theorem circlePhase_true : circlePhase true = 1 / 4 := rfl

/-- The literal positive small circle, shifted to the phase of the actual two-arc cover. -/
def shiftedCircle (b : Bool) (r : SmallRadius) : C(ℝ, TwicePuncturedPlane) :=
  (radialCoordinate b).comp
    ⟨fun t => (r, t + circlePhase b), continuous_const.prodMk (continuous_id.add continuous_const)⟩

@[simp] theorem shiftedCircle_radialCoordinate (b : Bool) (r : SmallRadius) (t : ℝ) :
    shiftedCircle b r t = radialCoordinate b (r, t + circlePhase b) := rfl

@[simp] theorem shiftedCircle_coe (b : Bool) (r : SmallRadius) (t : ℝ) :
    (shiftedCircle b r t : ℂ) =
      if b then 1 - circleMap 0 (r : ℝ) (2 * Real.pi * (t + circlePhase b))
      else circleMap 0 (r : ℝ) (2 * Real.pi * (t + circlePhase b)) := rfl

/-- The real coordinate records the slit-overlap order for either puncture. -/
theorem shiftedCircle_re (b : Bool) (r : SmallRadius) (t : ℝ) :
    (shiftedCircle b r t : ℂ).re =
      (if b then 1 else 0) + (r : ℝ) * Real.sin (2 * Real.pi * t) := by
  cases b
  · change (circleMap 0 (r : ℝ) (2 * Real.pi * (t + 3 / 4))).re =
      0 + (r : ℝ) * Real.sin (2 * Real.pi * t)
    rw [circleMap_zero_re,
      show 2 * Real.pi * (t + 3 / 4) = (2 * Real.pi * t + Real.pi) + Real.pi / 2 by ring,
      Real.cos_add_pi_div_two, Real.sin_add_pi, neg_neg, zero_add]
  · change (1 - circleMap 0 (r : ℝ) (2 * Real.pi * (t + 1 / 4))).re =
      1 + (r : ℝ) * Real.sin (2 * Real.pi * t)
    rw [Complex.sub_re, Complex.one_re, circleMap_zero_re,
      show 2 * Real.pi * (t + 1 / 4) = 2 * Real.pi * t + Real.pi / 2 by ring,
      Real.cos_add_pi_div_two]
    ring

/-- Both chosen phases start below the puncture and have the same imaginary coordinate. -/
theorem shiftedCircle_im (b : Bool) (r : SmallRadius) (t : ℝ) :
    (shiftedCircle b r t : ℂ).im = -(r : ℝ) * Real.cos (2 * Real.pi * t) := by
  cases b
  · change (circleMap 0 (r : ℝ) (2 * Real.pi * (t + 3 / 4))).im =
      -(r : ℝ) * Real.cos (2 * Real.pi * t)
    rw [circleMap_zero_im,
      show 2 * Real.pi * (t + 3 / 4) = (2 * Real.pi * t + Real.pi) + Real.pi / 2 by ring,
      Real.sin_add_pi_div_two, Real.cos_add_pi]
    ring
  · change (1 - circleMap 0 (r : ℝ) (2 * Real.pi * (t + 1 / 4))).im =
      -(r : ℝ) * Real.cos (2 * Real.pi * t)
    rw [Complex.sub_im, Complex.one_im, circleMap_zero_im,
      show 2 * Real.pi * (t + 1 / 4) = 2 * Real.pi * t + Real.pi / 2 by ring,
      Real.sin_add_pi_div_two]
    ring

/-- The actual phased coordinate has the elementary sine-cosine form used for the slit bounds. -/
theorem shiftedCircle_eq_trig (b : Bool) (r : SmallRadius) (t : ℝ) :
    (shiftedCircle b r t : ℂ) = shiftedTrigPoint b r t :=
  Complex.ext (shiftedCircle_re b r t) (shiftedCircle_im b r t)

/-- The full open unit turn stays in the actual upper slit plane. -/
theorem shiftedCircle_upper (b : Bool) (r : SmallRadius) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : (shiftedCircle b r t : ℂ) ∈ upperSlitPlane := by
  rw [shiftedCircle_eq_trig]
  exact shiftedTrigPoint_upper b r ht0 ht1

/-- The turn centered at zero stays in the actual lower slit plane. -/
theorem shiftedCircle_lower (b : Bool) (r : SmallRadius) {t : ℝ}
    (ht0 : -(1 / 2 : ℝ) < t) (ht1 : t < 1 / 2) :
    (shiftedCircle b r t : ℂ) ∈ lowerSlitPlane := by
  rw [shiftedCircle_eq_trig]
  exact shiftedTrigPoint_lower b r ht0 ht1

theorem shiftedCircle_mem_upperSlit (b : Bool) (r : SmallRadius) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) : shiftedCircle b r t ∈ upperSlit :=
  shiftedCircle_upper b r ht0 ht1

theorem shiftedCircle_mem_lowerSlit (b : Bool) (r : SmallRadius) {t : ℝ}
    (ht0 : -(1 / 2 : ℝ) < t) (ht1 : t < 1 / 2) : shiftedCircle b r t ∈ lowerSlit :=
  shiftedCircle_lower b r ht0 ht1

private theorem smallCircle_period (r t : ℝ) :
    circleMap 0 r (2 * Real.pi * (t + 1)) = circleMap 0 r (2 * Real.pi * t) := by
  rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring]
  exact periodic_circleMap (0 : ℂ) r (2 * Real.pi * t)

/-- The actual phased complex curve is one-periodic as a map into the punctured plane. -/
theorem shiftedCircle_periodic (b : Bool) (r : SmallRadius) :
    Function.Periodic (shiftedCircle b r) 1 := by
  intro t
  apply Subtype.ext
  rw [shiftedCircle_coe, shiftedCircle_coe,
    show t + 1 + circlePhase b = (t + circlePhase b) + 1 by ring, smallCircle_period]

theorem shiftedCircle_add_one (b : Bool) (r : SmallRadius) (t : ℝ) :
    shiftedCircle b r (t + 1) = shiftedCircle b r t := shiftedCircle_periodic b r t

/-- All integer translates have exactly the same value in the actual base. -/
theorem shiftedCircle_add_int (b : Bool) (r : SmallRadius) (t : ℝ) (k : ℤ) :
    shiftedCircle b r (t + (k : ℝ)) = shiftedCircle b r t := by
  simpa only [mul_one] using (shiftedCircle_periodic b r).int_mul k t

private theorem circle_full_turn (r : ℝ) : circleMap 0 r (2 * Real.pi) = (r : ℂ) := by
  simp [circleMap]

private theorem circle_half_turn (r : ℝ) : circleMap 0 r Real.pi = -(r : ℂ) := by
  simp [circleMap, Complex.exp_pi_mul_I]

private theorem circle_three_half_turn (r : ℝ) :
    circleMap 0 r (3 * Real.pi) = -(r : ℂ) := by
  rw [show (3 : ℝ) * Real.pi = Real.pi + 2 * Real.pi by ring,
    periodic_circleMap, circle_half_turn]

/-- At one quarter, the zero circle is in the middle and the one circle is on the right. -/
theorem shiftedCircle_quarter_coe (b : Bool) (r : SmallRadius) :
    (shiftedCircle b r (1 / 4) : ℂ) = if b then (1 : ℂ) + (r : ℝ) else (r : ℝ) := by
  cases b
  · change circleMap 0 (r : ℝ) (2 * Real.pi * ((1 / 4 : ℝ) + 3 / 4)) = (r : ℂ)
    rw [show 2 * Real.pi * ((1 / 4 : ℝ) + 3 / 4) = 2 * Real.pi by ring, circle_full_turn]
  · change 1 - circleMap 0 (r : ℝ) (2 * Real.pi * ((1 / 4 : ℝ) + 1 / 4)) = 1 + (r : ℂ)
    rw [show 2 * Real.pi * ((1 / 4 : ℝ) + 1 / 4) = Real.pi by ring, circle_half_turn]
    ring

/-- At three quarters, the zero circle is on the left and the one circle is in the middle. -/
theorem shiftedCircle_threeQuarter_coe (b : Bool) (r : SmallRadius) :
    (shiftedCircle b r (3 / 4) : ℂ) = if b then (1 : ℂ) - (r : ℝ) else -(r : ℝ) := by
  cases b
  · change circleMap 0 (r : ℝ) (2 * Real.pi * ((3 / 4 : ℝ) + 3 / 4)) = -(r : ℂ)
    rw [show 2 * Real.pi * ((3 / 4 : ℝ) + 3 / 4) = 3 * Real.pi by ring,
      circle_three_half_turn]
  · change 1 - circleMap 0 (r : ℝ) (2 * Real.pi * ((3 / 4 : ℝ) + 1 / 4)) = 1 - (r : ℂ)
    rw [show 2 * Real.pi * ((3 / 4 : ℝ) + 1 / 4) = 2 * Real.pi by ring, circle_full_turn]

/-- The quarter-time point lies in the literal geometric overlap component. -/
theorem shiftedCircle_quarter_overlap (b : Bool) (r : SmallRadius) :
    shiftedCircle b r (1 / 4) ∈ slitOverlapStrip (if b then 2 else 1) := by
  rw [mem_slitOverlapStrip, shiftedCircle_quarter_coe]
  cases b
  · change 0 < (r : ℝ) ∧ (r : ℝ) < 1
    exact ⟨r.property.1, lt_of_le_of_lt r.property.2 (by norm_num)⟩
  · change 1 < 1 + (r : ℝ)
    linarith [r.property.1]

/-- The three-quarter-time point lies in the other literal geometric overlap component. -/
theorem shiftedCircle_threeQuarter_overlap (b : Bool) (r : SmallRadius) :
    shiftedCircle b r (3 / 4) ∈ slitOverlapStrip (if b then 1 else 0) := by
  rw [mem_slitOverlapStrip, shiftedCircle_threeQuarter_coe]
  cases b
  · change -(r : ℝ) < 0
    linarith [r.property.1]
  · change 0 < 1 - (r : ℝ) ∧ 1 - (r : ℝ) < 1
    constructor <;> linarith [r.property.1, r.property.2]

/-- Without the phase shift, the outer coordinate is the existing actual positive meridian. -/
theorem radialCoordinate_outer_positiveMeridian (b : Bool) (t : unitInterval) :
    radialCoordinate b (outerRadius, (t : ℝ)) =
      if b then positiveMeridianOne t else positiveMeridianZero t := by
  cases b
  · apply Subtype.ext
    change circleMap 0 (1 / 2) (2 * Real.pi * (t : ℝ)) = (positiveMeridianZero t : ℂ)
    exact (positiveMeridianZero_eq_circleMap t).symm
  · apply Subtype.ext
    change 1 - circleMap 0 (1 / 2) (2 * Real.pi * (t : ℝ)) = (positiveMeridianOne t : ℂ)
    rw [← positiveMeridianZero_eq_circleMap, positiveMeridianZero_apply, positiveMeridianOne_apply]

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryCircleSlits
