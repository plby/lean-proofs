import StackExchange.Puzzling139335.AcuteCorner.Defs
import StackExchange.Puzzling139335.BoundaryGerm

/-!
# Global coordinate signs from a filled cone germ

An origin-fixing affine isometry carries positive scalar multiples to
positive scalar multiples. Thus an image cone agreeing near the origin
with a subset of the square is entirely contained in the first quadrant.
-/

open Set Metric

namespace Puzzling139335.N6.TwoDouble.UnitRay.GermPlacement

open AcuteCorner

/-- An origin-fixing affine isometry agrees with its linear part. -/
theorem linear_apply_of_zero (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (x : Plane) : e.linearIsometryEquiv x = e x := by
  simpa only [vsub_eq_sub, sub_zero, he0] using e.map_vsub x 0

/-- In particular it commutes with scalar multiplication. -/
theorem map_smul_of_zero (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (t : ℝ) (x : Plane) : e (t • x) = t • e x := by
  rw [← linear_apply_of_zero e he0, map_smul, linear_apply_of_zero e he0]

/-- Every nonnegative scalar multiple of a point in the image cone remains
in that same image cone. -/
theorem smul_mem_image_cone45 (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    {x : Plane} (hx : x ∈ e '' cone45) {t : ℝ} (ht : 0 ≤ t) :
    t • x ∈ e '' cone45 := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨t • y, ?_, map_smul_of_zero e he0 t y⟩
  change 0 ≤ t * y 1 ∧ t * y 1 ≤ t * y 0
  exact ⟨mul_nonneg ht hy.1, mul_le_mul_of_nonneg_left hy.2 ht⟩

/-- A filled cone germ belonging locally to the square forces both
coordinates of every point in the entire cone to be nonnegative. -/
theorem image_cone45_coordinates_nonneg {P : Set Plane}
    (hPsub : P ⊆ unitSquare) (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hgerm : SameBoundaryGerm P (e '' cone45) 0) :
    ∀ x ∈ e '' cone45, 0 ≤ x 0 ∧ 0 ≤ x 1 := by
  obtain ⟨r, hr, heq⟩ := hgerm
  intro x hx
  let t : ℝ := r / (2 * (‖x‖ + 1))
  have hdenom : 0 < 2 * (‖x‖ + 1) := by positivity
  have ht : 0 < t := div_pos hr hdenom
  have hteq : t * (2 * (‖x‖ + 1)) = r :=
    div_mul_cancel₀ r (ne_of_gt hdenom)
  have htxnorm : t * ‖x‖ < r := by
    nlinarith only [hteq, ht, mul_nonneg ht.le (norm_nonneg x)]
  have htxball : t • x ∈ ball (0 : Plane) r := by
    apply mem_ball.mpr
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact htxnorm
  have htxP : t • x ∈ P :=
    ((Set.ext_iff.mp heq (t • x)).mpr
      ⟨htxball, smul_mem_image_cone45 e he0 hx ht.le⟩).2
  have htx0 : 0 ≤ t * x 0 := (hPsub htxP).1.1
  have htx1 : 0 ≤ t * x 1 := (hPsub htxP).2.1
  exact ⟨(mul_nonneg_iff_of_pos_left ht).mp htx0,
    (mul_nonneg_iff_of_pos_left ht).mp htx1⟩

/-- Membership of the origin follows directly from the filled cone germ. -/
theorem zero_mem_of_image_cone45_germ {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0)
    (hgerm : SameBoundaryGerm P (e '' cone45) 0) : (0 : Plane) ∈ P := by
  obtain ⟨r, hr, heq⟩ := hgerm
  have hcone : (0 : Plane) ∈ cone45 := ⟨le_rfl, le_rfl⟩
  exact ((Set.ext_iff.mp heq 0).mpr ⟨mem_ball_self hr, ⟨0, hcone, he0⟩⟩).2

end Puzzling139335.N6.TwoDouble.UnitRay.GermPlacement
