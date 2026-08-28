import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryRadiusCore
import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupCoverSets

/-!
# Slit membership of the phase-shifted boundary circles

The circles start below their punctures.  The interval of turns `(0, 1)`
lies in the upper slit plane, and `(-1/2, 1/2)` lies in the lower slit
plane.  The radius bound separates each circle from the other puncture.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryCircleSlits

open SpecialPeriods.Triangle

/-- The boundary circle centered at the selected puncture, starting directly below it. -/
def shiftedTrigPoint (b : Bool) (r : BoundaryRadius.SmallRadius) (t : ℝ) : ℂ :=
  ⟨(if b then 1 else 0) + (r : ℝ) * Real.sin (2 * Real.pi * t),
    -(r : ℝ) * Real.cos (2 * Real.pi * t)⟩

private theorem shiftedTrigPoint_re_ne (b : Bool) (r : BoundaryRadius.SmallRadius)
    (t : ℝ) (hs : Real.sin (2 * Real.pi * t) ≠ 0) :
    (shiftedTrigPoint b r t).re ≠ 0 ∧ (shiftedTrigPoint b r t).re ≠ 1 := by
  have hp : (r : ℝ) * Real.sin (2 * Real.pi * t) ≠ 0 :=
    mul_ne_zero (ne_of_gt r.property.1) hs
  have hle : (r : ℝ) * Real.sin (2 * Real.pi * t) ≤ (r : ℝ) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.sin_le_one (2 * Real.pi * t)) r.property.1.le
  have hge : -(r : ℝ) ≤ (r : ℝ) * Real.sin (2 * Real.pi * t) := by
    simpa only [mul_neg, mul_one] using
      mul_le_mul_of_nonneg_left (Real.neg_one_le_sin (2 * Real.pi * t)) r.property.1.le
  have hr := r.property.2
  cases b with
  | false =>
    change 0 + (r : ℝ) * Real.sin (2 * Real.pi * t) ≠ 0 ∧
      0 + (r : ℝ) * Real.sin (2 * Real.pi * t) ≠ 1
    constructor
    · simpa only [zero_add] using hp
    · linarith
  | true =>
    change 1 + (r : ℝ) * Real.sin (2 * Real.pi * t) ≠ 0 ∧
      1 + (r : ℝ) * Real.sin (2 * Real.pi * t) ≠ 1
    constructor
    · linarith
    · intro h
      apply hp
      linarith

private theorem sin_two_pi_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    0 < Real.sin (2 * Real.pi * t) := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi ht0)
  calc
    2 * Real.pi * t < 2 * Real.pi * (1 / 2) := mul_lt_mul_of_pos_left ht1 hpi
    _ = Real.pi := by ring

private theorem sin_two_pi_neg {t : ℝ} (ht0 : -(1 / 2 : ℝ) < t) (ht1 : t < 0) :
    Real.sin (2 * Real.pi * t) < 0 := by
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  apply Real.sin_neg_of_neg_of_neg_pi_lt (mul_neg_of_pos_of_neg hpi ht1)
  calc
    -Real.pi = 2 * Real.pi * (-(1 / 2 : ℝ)) := by ring
    _ < 2 * Real.pi * t := mul_lt_mul_of_pos_left ht0 hpi

/-- Every turn strictly between zero and one belongs to the upper slit plane. -/
theorem shiftedTrigPoint_upper (b : Bool) (r : BoundaryRadius.SmallRadius)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    shiftedTrigPoint b r t ∈ upperSlitPlane := by
  rcases lt_trichotomy t (1 / 2) with h | h | h
  · exact Or.inr (shiftedTrigPoint_re_ne b r t (ne_of_gt (sin_two_pi_pos ht0 h)))
  · apply Or.inl
    change 0 < -(r : ℝ) * Real.cos (2 * Real.pi * t)
    rw [h, show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.cos_pi]
    simpa only [mul_neg, mul_one, neg_neg] using r.property.1
  · have hs := sin_two_pi_neg (t := t - 1) (by linarith) (by linarith)
    rw [show 2 * Real.pi * (t - 1) = 2 * Real.pi * t - 2 * Real.pi by ring,
      Real.sin_sub_two_pi] at hs
    exact Or.inr (shiftedTrigPoint_re_ne b r t (ne_of_lt hs))

/-- Every turn strictly between minus one half and one half belongs to the lower slit plane. -/
theorem shiftedTrigPoint_lower (b : Bool) (r : BoundaryRadius.SmallRadius)
    {t : ℝ} (ht0 : -(1 / 2 : ℝ) < t) (ht1 : t < 1 / 2) :
    shiftedTrigPoint b r t ∈ lowerSlitPlane := by
  rcases lt_trichotomy t 0 with h | h | h
  · exact Or.inr (shiftedTrigPoint_re_ne b r t (ne_of_lt (sin_two_pi_neg ht0 h)))
  · apply Or.inl
    change -(r : ℝ) * Real.cos (2 * Real.pi * t) < 0
    rw [h, mul_zero, Real.cos_zero, mul_one]
    exact neg_neg_of_pos r.property.1
  · exact Or.inr (shiftedTrigPoint_re_ne b r t (ne_of_gt (sin_two_pi_pos h ht1)))

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryCircleSlits
