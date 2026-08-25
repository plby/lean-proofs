import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Scalar obstruction for a half-turned middle pair

The strict unit-square coordinate bounds for either sign of a nonaxis
placement angle force the intrinsic horizontal coordinate below `1 / 2`.
-/

namespace Puzzling139335.N4MiddleInvolutions.HalfTurn

/-- Positive coordinates on the unit circle satisfy the strict inequality
needed after taking the weighted sum of the placement bounds. -/
theorem add_lt_one_add_mul_of_sq_add_sq_eq_one {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hunit : a ^ 2 + b ^ 2 = 1) :
    a + b < 1 + a * b := by
  have ha1 : a < 1 := by
    nlinarith only [hunit, sq_pos_of_pos hb, sq_nonneg (a - 1)]
  have hb1 : b < 1 := by
    nlinarith only [hunit, sq_pos_of_pos ha, sq_nonneg (b - 1)]
  nlinarith only [mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hb1)]

/-- Weighting the two coordinate bounds cancels the vertical coordinate.
No bound on that coordinate is needed for this scalar implication. -/
theorem lt_half_of_placement_bounds {a b u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hunit : a ^ 2 + b ^ 2 = 1)
    (hfirst : b * u + a * v < 1 / 2)
    (hsecond : a * u + b * (1 / 2 - v) < 1 / 2) :
    u < 1 / 2 := by
  have hfirst' := mul_lt_mul_of_pos_left hfirst hb
  have hsecond' := mul_lt_mul_of_pos_left hsecond ha
  have hunitu : (a ^ 2 + b ^ 2) * u = u := by
    rw [hunit, one_mul]
  have hsum := add_lt_one_add_mul_of_sq_add_sq_eq_one ha hb hunit
  nlinarith only [hfirst', hsecond', hunitu, hsum]

/-- Neither sign of a nonaxis placement angle is compatible with the
half-unit lower bound on the intrinsic horizontal coordinate. -/
theorem placement_bounds_impossible {a b u v : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hunit : a ^ 2 + b ^ 2 = 1)
    (hu : 1 / 2 ≤ u) (_hv0 : 0 ≤ v) (_hv1 : v ≤ 1 / 2)
    (hbounds :
      (b * u + a * v < 1 / 2 ∧ a * u + b * (1 / 2 - v) < 1 / 2) ∨
      (a * u + b * v < 1 / 2 ∧ b * u + a * (1 / 2 - v) < 1 / 2)) :
    False := by
  rcases hbounds with hbounds | hbounds
  · exact (not_lt_of_ge hu)
      (lt_half_of_placement_bounds ha hb hunit hbounds.1 hbounds.2)
  · have hunit' : b ^ 2 + a ^ 2 = 1 := by
      simpa only [add_comm] using hunit
    exact (not_lt_of_ge hu)
      (lt_half_of_placement_bounds hb ha hunit' hbounds.1 hbounds.2)

/-- Absolute coordinate bounds exclude every choice of signs for the
nonzero coordinates of the placement's unit direction. -/
theorem abs_placement_bounds_impossible {c s u v : ℝ}
    (hc : c ≠ 0) (hs : s ≠ 0) (hunit : c ^ 2 + s ^ 2 = 1)
    (hu : 1 / 2 ≤ u) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2)
    (hxA : |c * u - s * v| < 1 / 2)
    (hyA : |s * u + c * v| < 1 / 2)
    (hxM : |c * u + s * (1 / 2 - v)| < 1 / 2)
    (hyM : |s * u - c * (1 / 2 - v)| < 1 / 2) : False := by
  rcases lt_or_gt_of_ne hc with hc | hc
  · rcases lt_or_gt_of_ne hs with hs | hs
    · exact placement_bounds_impossible (neg_pos.mpr hc) (neg_pos.mpr hs)
        (by nlinarith only [hunit]) hu hv0 hv1 (Or.inl ⟨
          by nlinarith only [(abs_lt.mp hyA).1],
          by nlinarith only [(abs_lt.mp hxM).1]⟩)
    · exact placement_bounds_impossible (neg_pos.mpr hc) hs
        (by nlinarith only [hunit]) hu hv0 hv1 (Or.inr ⟨
          by nlinarith only [(abs_lt.mp hxA).1],
          by nlinarith only [(abs_lt.mp hyM).2]⟩)
  · rcases lt_or_gt_of_ne hs with hs | hs
    · exact placement_bounds_impossible hc (neg_pos.mpr hs)
        (by nlinarith only [hunit]) hu hv0 hv1 (Or.inr ⟨
          by nlinarith only [(abs_lt.mp hxA).2],
          by nlinarith only [(abs_lt.mp hyM).1]⟩)
    · exact placement_bounds_impossible hc hs hunit hu hv0 hv1
        (Or.inl ⟨(abs_lt.mp hyA).2, (abs_lt.mp hxM).2⟩)

end Puzzling139335.N4MiddleInvolutions.HalfTurn
