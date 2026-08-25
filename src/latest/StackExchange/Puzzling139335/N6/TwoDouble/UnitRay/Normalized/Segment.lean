import StackExchange.Puzzling139335.BoundaryGerm

/-!
# Sampling actual unit segments in a boundary germ

The sample has a strictly positive parameter, so homogeneous coordinate
conditions transfer back to the whole ray.  A positive diagonal segment of
unit length contains the square center by an explicit segment parameter.
-/

open Set Metric

namespace Puzzling139335.N6.TwoDouble.UnitRay

/-- Every positive scalar multiple with scalar at most one lies in the
actual segment from the origin to its endpoint. -/
theorem smul_mem_segment_zero {w : Plane} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • w ∈ segment ℝ (0 : Plane) w := by
  exact ⟨1 - t, t, sub_nonneg.mpr ht1, ht0, by ring, by simp⟩

/-- An actual unit segment in the first set has a strictly positive sample
in any second set with the same germ at the origin. -/
theorem unit_segment_germ_sample {A B : Set Plane} {w : Plane}
    (hgerm : SameBoundaryGerm A B 0) (hseg : segment ℝ 0 w ⊆ A)
    (hnorm : ‖w‖ = 1) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t • w ∈ B := by
  obtain ⟨r, hr, heq⟩ := hgerm
  let t : ℝ := min (r / 2) (1 / 2)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have htr : t < r := (min_le_left _ _).trans_lt (by linarith only [hr])
  have htball : t • w ∈ ball (0 : Plane) r := by
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht, hnorm, mul_one] using htr
  refine ⟨t, ht, ht1, ?_⟩
  exact ((Set.ext_iff.mp heq (t • w)).mp
    ⟨htball, hseg (smul_mem_segment_zero ht.le ht1)⟩).2

/-- A nonnegative diagonal unit segment reaches past the square center.
The conclusion uses the actual segment, not a convex hull edge. -/
theorem center_mem_of_diagonal_unit_segment {A : Set Plane} {w : Plane}
    (hseg : segment ℝ 0 w ⊆ A) (hnorm : ‖w‖ = 1)
    (hx : 0 ≤ w 0) (hdiag : w 0 = w 1) : squareCenter ∈ A := by
  have hsq : w 0 ^ 2 + w 1 ^ 2 = 1 := by
    calc
      _ = ‖w‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
      _ = 1 := by rw [hnorm]; norm_num
  have hxhalf : (1 / 2 : ℝ) ≤ w 0 := by
    apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hx).mp
    rw [← hdiag] at hsq
    nlinarith only [hsq]
  have hxpos : 0 < w 0 := lt_of_lt_of_le (by norm_num) hxhalf
  let t : ℝ := (1 / 2) / w 0
  have ht0 : 0 ≤ t := (div_pos (by norm_num) hxpos).le
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hxpos).mpr
    simpa only [one_mul] using hxhalf
  have hpoint : t • w = squareCenter := by
    ext i
    fin_cases i
    · change ((1 / 2 : ℝ) / w 0) * w 0 = 1 / 2
      exact div_mul_cancel₀ _ hxpos.ne'
    · change ((1 / 2 : ℝ) / w 0) * w 1 = 1 / 2
      rw [← hdiag]
      exact div_mul_cancel₀ _ hxpos.ne'
  exact hpoint ▸ hseg (smul_mem_segment_zero ht0 ht1)

end Puzzling139335.N6.TwoDouble.UnitRay
