import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupMeridians

/-!
# Explicit positive outer circles and their based tails

For every real radius `R ≥ 2`, the circle centered at `1/2`, starting at
its bottom point, avoids both punctures and makes one positive turn.
The vertical tail from `1/2` to that bottom point lies in both slit
domains. The circle splits into lower, upper, and lower slit-domain
arcs at the quarter and three-quarter parameters.
-/

noncomputable section

open Set Complex
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The exact complex-coordinate formula for a positive outer circle. -/
def outerCircleValue (R t : ℝ) : ℂ :=
  circleMap (1 / 2 : ℂ) R (-Real.pi / 2 + 2 * Real.pi * t)

@[fun_prop] theorem continuous_outerCircleValue (R : ℝ) :
    Continuous (outerCircleValue R) := by
  unfold outerCircleValue circleMap
  fun_prop

@[simp] theorem outerCircleValue_zero (R : ℝ) :
    outerCircleValue R 0 = (1 / 2 : ℂ) - (R : ℂ) * I := by
  simpa only [outerCircleValue, mul_zero, add_zero] using
    circleMap_neg_pi_div_two (1 / 2 : ℂ) R

@[simp] theorem outerCircleValue_one (R : ℝ) :
    outerCircleValue R 1 = (1 / 2 : ℂ) - (R : ℂ) * I := by
  unfold outerCircleValue
  rw [mul_one, periodic_circleMap (1 / 2 : ℂ) R (-Real.pi / 2)]
  exact circleMap_neg_pi_div_two (1 / 2 : ℂ) R

/-- Every point has the prescribed radius about the center `1/2`. -/
theorem outerCircleValue_norm_sub_center (R : ℝ) (hR : 2 ≤ R) (t : ℝ) :
    ‖outerCircleValue R t - (1 / 2 : ℂ)‖ = R := by
  simp only [outerCircleValue, circleMap_sub_center, norm_circleMap_zero]
  exact abs_of_nonneg (by linarith)

theorem outerCircleValue_avoids_punctures (R : ℝ) (hR : 2 ≤ R) (t : ℝ) :
    outerCircleValue R t ≠ 0 ∧ outerCircleValue R t ≠ 1 := by
  have hn := outerCircleValue_norm_sub_center R hR t
  constructor
  · intro h
    rw [h] at hn
    norm_num [norm_div] at hn
    linarith
  · intro h
    rw [h, show (1 : ℂ) - 1 / 2 = 1 / 2 by ring] at hn
    norm_num [norm_div] at hn
    linarith

/-- The bottom point of the radius-`R` outer circle. -/
def outerCircleBasepoint (R : ℝ) (hR : 2 ≤ R) : TwicePuncturedPlane :=
  ⟨(1 / 2 : ℂ) - (R : ℂ) * I, by
    rw [← outerCircleValue_zero R]
    exact outerCircleValue_avoids_punctures R hR 0⟩

@[simp] theorem outerCircleBasepoint_coe (R : ℝ) (hR : 2 ≤ R) :
    (outerCircleBasepoint R hR : ℂ) = (1 / 2 : ℂ) - (R : ℂ) * I := rfl

/-- The genuine positively oriented outer loop in the twice-punctured plane. -/
def outerPositiveCircle (R : ℝ) (hR : 2 ≤ R) :
    Path (outerCircleBasepoint R hR) (outerCircleBasepoint R hR) where
  toFun t := ⟨outerCircleValue R t, outerCircleValue_avoids_punctures R hR t⟩
  continuous_toFun :=
    ((continuous_outerCircleValue R).comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext (outerCircleValue_zero R)
  target' := Subtype.ext (outerCircleValue_one R)

@[simp] theorem outerPositiveCircle_coe (R : ℝ) (hR : 2 ≤ R) (t : unitInterval) :
    (outerPositiveCircle R hR t : ℂ) =
      circleMap (1 / 2 : ℂ) R (-Real.pi / 2 + 2 * Real.pi * (t : ℝ)) := rfl

theorem outerPositiveCircle_norm_sub_center (R : ℝ) (hR : 2 ≤ R) (t : unitInterval) :
    ‖(outerPositiveCircle R hR t : ℂ) - (1 / 2 : ℂ)‖ = R :=
  outerCircleValue_norm_sub_center R hR t

/-- The straight vertical segment from the common basepoint to the circle. -/
def outerTailValue (R t : ℝ) : ℂ := (1 / 2 : ℂ) - ((R * t : ℝ) : ℂ) * I

@[simp] theorem outerTailValue_re (R t : ℝ) : (outerTailValue R t).re = 1 / 2 := by
  simp [outerTailValue, Complex.mul_re]

theorem outerTailValue_mem_slitPlanes (R t : ℝ) :
    outerTailValue R t ∈ upperSlitPlane ∩ lowerSlitPlane := by
  have hx : (outerTailValue R t).re ≠ 0 ∧ (outerTailValue R t).re ≠ 1 := by
    rw [outerTailValue_re]
    norm_num
  exact ⟨Or.inr hx, Or.inr hx⟩

/-- The actual based vertical tail, with its full image in both slit domains. -/
def outerMeridianTail (R : ℝ) (hR : 2 ≤ R) :
    Path meridianBasepoint (outerCircleBasepoint R hR) where
  toFun t := ⟨outerTailValue R t,
    upperSlitPlane_subset_punctured (outerTailValue_mem_slitPlanes R t).1⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold outerTailValue
    fun_prop
  source' := Subtype.ext (by simp [outerTailValue])
  target' := Subtype.ext (by simp [outerTailValue])

@[simp] theorem outerMeridianTail_coe (R : ℝ) (hR : 2 ≤ R) (t : unitInterval) :
    (outerMeridianTail R hR t : ℂ) =
      (1 / 2 : ℂ) - ((R * (t : ℝ) : ℝ) : ℂ) * I := rfl

theorem outerMeridianTail_mem_upperSlitPlane (R : ℝ) (hR : 2 ≤ R) (t : unitInterval) :
    (outerMeridianTail R hR t : ℂ) ∈ upperSlitPlane :=
  (outerTailValue_mem_slitPlanes R t).1

theorem outerMeridianTail_mem_lowerSlitPlane (R : ℝ) (hR : 2 ≤ R) (t : unitInterval) :
    (outerMeridianTail R hR t : ℂ) ∈ lowerSlitPlane :=
  (outerTailValue_mem_slitPlanes R t).2

/-- The rightmost point is reached after a quarter turn. -/
def outerQuarter : unitInterval := ⟨1 / 4, by norm_num⟩

/-- The leftmost point is reached after three quarters of a turn. -/
def outerThreeQuarters : unitInterval := ⟨3 / 4, by norm_num⟩

@[simp] theorem outerQuarter_coe : (outerQuarter : ℝ) = 1 / 4 := rfl

@[simp] theorem outerThreeQuarters_coe : (outerThreeQuarters : ℝ) = 3 / 4 := rfl

theorem outerCircleValue_quarter (R : ℝ) :
    outerCircleValue R (1 / 4) = (1 / 2 : ℂ) + (R : ℂ) := by
  unfold outerCircleValue
  rw [show -Real.pi / 2 + 2 * Real.pi * (1 / 4) = 0 by ring]
  simp [circleMap]

theorem outerCircleValue_threeQuarters (R : ℝ) :
    outerCircleValue R (3 / 4) = (1 / 2 : ℂ) - (R : ℂ) := by
  unfold outerCircleValue
  rw [show -Real.pi / 2 + 2 * Real.pi * (3 / 4) = Real.pi by ring]
  simp [circleMap, Complex.exp_pi_mul_I, sub_eq_add_neg]

theorem outerCircleValue_im (R t : ℝ) :
    (outerCircleValue R t).im = R * Real.sin (-Real.pi / 2 + 2 * Real.pi * t) := by
  simpa [outerCircleValue, circleMap] using
    circleMap_zero_im R (-Real.pi / 2 + 2 * Real.pi * t)

theorem outerCircleValue_mem_lowerSlitPlane (R : ℝ) (hR : 2 ≤ R) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ht : t ≤ 1 / 4 ∨ 3 / 4 ≤ t) :
    outerCircleValue R t ∈ lowerSlitPlane := by
  by_cases hquarter : t = 1 / 4
  · rw [hquarter, outerCircleValue_quarter]
    norm_num [lowerSlitPlane]
    constructor <;> linarith
  by_cases hthree : t = 3 / 4
  · rw [hthree, outerCircleValue_threeQuarters]
    norm_num [lowerSlitPlane]
    constructor <;> linarith
  apply Or.inl
  rw [outerCircleValue_im]
  have hRpos : 0 < R := by linarith
  apply mul_neg_of_pos_of_neg hRpos
  rcases ht with ht | ht
  · have htlt : t < 1 / 4 := lt_of_le_of_ne ht hquarter
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  · have htlt : 3 / 4 < t := lt_of_le_of_ne ht (Ne.symm hthree)
    have hsin : 0 < Real.sin ((-Real.pi / 2 + 2 * Real.pi * t) - Real.pi) := by
      apply Real.sin_pos_of_pos_of_lt_pi
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    rw [Real.sin_sub_pi] at hsin
    linarith

theorem outerCircleValue_mem_upperSlitPlane (R : ℝ) (hR : 2 ≤ R) (t : ℝ)
    (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 3 / 4) :
    outerCircleValue R t ∈ upperSlitPlane := by
  by_cases hquarter : t = 1 / 4
  · rw [hquarter, outerCircleValue_quarter]
    norm_num [upperSlitPlane]
    constructor <;> linarith
  by_cases hthree : t = 3 / 4
  · rw [hthree, outerCircleValue_threeQuarters]
    norm_num [upperSlitPlane]
    constructor <;> linarith
  apply Or.inl
  rw [outerCircleValue_im]
  have hRpos : 0 < R := by linarith
  apply mul_pos hRpos
  have ht0lt : 1 / 4 < t := lt_of_le_of_ne ht0 (Ne.symm hquarter)
  have ht1lt : t < 3 / 4 := lt_of_le_of_ne ht1 hthree
  apply Real.sin_pos_of_pos_of_lt_pi
  · nlinarith [Real.pi_pos]
  · nlinarith [Real.pi_pos]

/-- The first cut is the actual rightmost point of the circle. -/
@[simp] theorem outerPositiveCircle_quarter (R : ℝ) (hR : 2 ≤ R) :
    (outerPositiveCircle R hR outerQuarter : ℂ) = (1 / 2 : ℂ) + (R : ℂ) :=
  outerCircleValue_quarter R

/-- The second cut is the actual leftmost point of the circle. -/
@[simp] theorem outerPositiveCircle_threeQuarters (R : ℝ) (hR : 2 ≤ R) :
    (outerPositiveCircle R hR outerThreeQuarters : ℂ) = (1 / 2 : ℂ) - (R : ℂ) :=
  outerCircleValue_threeQuarters R

theorem outerPositiveCircle_mem_lowerSlitPlane (R : ℝ) (hR : 2 ≤ R) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 4 ∨ 3 / 4 ≤ (t : ℝ)) :
    (outerPositiveCircle R hR t : ℂ) ∈ lowerSlitPlane :=
  outerCircleValue_mem_lowerSlitPlane R hR t t.property.1 t.property.2 ht

theorem outerPositiveCircle_mem_upperSlitPlane (R : ℝ) (hR : 2 ≤ R) (t : unitInterval)
    (ht0 : 1 / 4 ≤ (t : ℝ)) (ht1 : (t : ℝ) ≤ 3 / 4) :
    (outerPositiveCircle R hR t : ℂ) ∈ upperSlitPlane :=
  outerCircleValue_mem_upperSlitPlane R hR t ht0 ht1

theorem outerPositiveCircle_quarter_re_gt_one (R : ℝ) (hR : 2 ≤ R) :
    1 < (outerPositiveCircle R hR outerQuarter : ℂ).re := by
  rw [outerPositiveCircle_quarter]
  norm_num
  linarith

theorem outerPositiveCircle_threeQuarters_re_lt_zero (R : ℝ) (hR : 2 ≤ R) :
    (outerPositiveCircle R hR outerThreeQuarters : ℂ).re < 0 := by
  rw [outerPositiveCircle_threeQuarters]
  norm_num
  linarith

theorem outerCircle_zero_mem_ball (R : ℝ) (hR : 2 ≤ R) :
    (0 : ℂ) ∈ Metric.ball (1 / 2 : ℂ) R := by
  norm_num [Metric.mem_ball, dist_eq_norm, norm_div]
  linarith

theorem outerCircle_one_mem_ball (R : ℝ) (hR : 2 ≤ R) :
    (1 : ℂ) ∈ Metric.ball (1 / 2 : ℂ) R := by
  rw [Metric.mem_ball, dist_eq_norm, show (1 : ℂ) - 1 / 2 = 1 / 2 by ring]
  norm_num [norm_div]
  linarith

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
