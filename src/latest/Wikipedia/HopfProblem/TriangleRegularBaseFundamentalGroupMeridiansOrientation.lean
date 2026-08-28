import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupMeridiansPaths
import Mathlib.Tactic.Ring

/-!
# The positive orientation of the two concrete meridians

Concatenating the indicated semicircles gives the usual full circles
about zero and one, with positive radius `1/2` and increasing angle
through exactly `2π`.  The identities below are pointwise identities of
the actual paths; no winding number or presentation of the fundamental
group is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

private theorem trans_symm_exp_apply {x y : ℂ} (a b : Path x y) (c r : ℂ)
    (ha : ∀ t : unitInterval,
      a t = c + r * Complex.exp ((Real.pi : ℂ) * Complex.I * (t : ℝ)))
    (hb : ∀ t : unitInterval,
      b t = c + r * Complex.exp (-((Real.pi : ℂ) * Complex.I * (t : ℝ))))
    (t : unitInterval) :
    (a.trans b.symm) t =
      c + r * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (t : ℝ)) := by
  rw [Path.trans_apply]
  split_ifs with ht
  · rw [ha]
    apply congrArg (fun u : ℂ => c + r * Complex.exp u)
    push_cast
    ring
  · rw [Path.symm_apply, Function.comp_apply, hb]
    simp only [unitInterval.coe_symm_eq]
    have he : -((Real.pi : ℂ) * Complex.I * ((1 - (2 * (t : ℝ) - 1) : ℝ) : ℂ)) =
        (2 * Real.pi : ℂ) * Complex.I * (t : ℝ) - 2 * Real.pi * Complex.I := by
      push_cast
      ring
    rw [he, Complex.exp_periodic.sub_eq]

/-- The meridian about zero first follows the upper semicircle. -/
def meridianZeroComplex : Path (1 / 2 : ℂ) (1 / 2) :=
  upperZeroArc.trans lowerZeroArc.symm

/-- The meridian about one first follows the lower semicircle. -/
def meridianOneComplex : Path (1 / 2 : ℂ) (1 / 2) :=
  lowerOneArc.trans upperOneArc.symm

@[simp] theorem meridianZeroComplex_apply (t : unitInterval) :
    meridianZeroComplex t =
      (1 / 2 : ℂ) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (t : ℝ)) := by
  simpa only [meridianZeroComplex, zero_add] using
    trans_symm_exp_apply upperZeroArc lowerZeroArc 0 (1 / 2)
      (fun s => by simpa only [zero_add] using upperZeroArc_apply s)
      (fun s => by simpa only [zero_add] using lowerZeroArc_apply s) t

@[simp] theorem meridianOneComplex_apply (t : unitInterval) :
    meridianOneComplex t =
      1 - (1 / 2 : ℂ) * Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (t : ℝ)) := by
  simpa only [meridianOneComplex, neg_mul, ← sub_eq_add_neg] using
    trans_symm_exp_apply lowerOneArc upperOneArc 1 (-(1 / 2))
      (fun s => by simpa only [neg_mul, ← sub_eq_add_neg] using lowerOneArc_apply s)
      (fun s => by simpa only [neg_mul, ← sub_eq_add_neg] using upperOneArc_apply s) t

/-- The zero meridian has positive radius and angle running from zero to `2π`. -/
theorem meridianZeroComplex_eq_circleMap (t : unitInterval) :
    meridianZeroComplex t = circleMap 0 (1 / 2) (2 * Real.pi * (t : ℝ)) := by
  rw [meridianZeroComplex_apply, circleMap_zero]
  push_cast
  apply congrArg (fun u : ℂ => (1 / 2 : ℂ) * Complex.exp u)
  ring

/-- The one meridian has positive radius and angle running from `π` to `3π`. -/
theorem meridianOneComplex_eq_circleMap (t : unitInterval) :
    meridianOneComplex t = circleMap 1 (1 / 2) (Real.pi + 2 * Real.pi * (t : ℝ)) := by
  rw [meridianOneComplex_apply]
  unfold circleMap
  push_cast
  have he : ((Real.pi : ℂ) + 2 * Real.pi * (t : ℝ)) * Complex.I =
      (2 * Real.pi : ℂ) * Complex.I * (t : ℝ) + Real.pi * Complex.I := by ring
  rw [he, Complex.exp_add_pi_mul_I]
  ring

/-- Both displayed circle parameters increase strictly, for either initial angle. -/
theorem meridian_angle_strictMono (θ : ℝ) :
    StrictMono (fun t : ℝ => θ + 2 * Real.pi * t) := by
  intro s t hst
  exact add_lt_add_right (mul_lt_mul_of_pos_left hst (mul_pos zero_lt_two Real.pi_pos)) θ

/-- Increasing the path parameter by one advances the angle by exactly one positive turn. -/
theorem meridian_angle_increment (θ t : ℝ) :
    (θ + 2 * Real.pi * (t + 1)) - (θ + 2 * Real.pi * t) = 2 * Real.pi := by
  ring

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
