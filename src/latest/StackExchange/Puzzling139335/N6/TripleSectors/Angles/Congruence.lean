import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Congruence.Rays
import StackExchange.Puzzling139335.N6.TripleSectors.Angles.Congruence.Matching

/-!
# Congruence preserves the opening angle of actual two-ray germs

The ray correspondence here follows from equality of the actual set germs
on positive-radius balls.  It is not an assumption about selected endpoints.
After the correspondence is established, preservation of Euclidean angles
gives the common angular width.  Reflections may exchange the two rays.
-/

open Set InnerProductGeometry

namespace Puzzling139335.N6.TripleSectors.Angles.Congruence

noncomputable section

/-- An actual congruence between two two-ray germs matches their rays,
possibly reversing their order. -/
theorem rays_match_of_boundary_germs
    {A B : Set Plane} {a b c d : Plane}
    (hA : SameBoundaryGerm A (segment ℝ 0 a ∪ segment ℝ 0 b) 0)
    (hB : SameBoundaryGerm B (segment ℝ 0 c ∪ segment ℝ 0 d) 0)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hzero : e 0 = 0) (he : e '' A = B)
    (hab : SegmentCrossing.det a b ≠ 0) :
    (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ e a = s • c ∧ e b = t • d) ∨
      (∃ s t : ℝ, 0 < s ∧ 0 < t ∧ e a = s • d ∧ e b = t • c) :=
  image_rays_match e hzero hab
    (image_left_ray_of_boundary_germs hA hB e hzero he
      (SegmentCrossing.left_ne_zero_of_det_ne_zero hab))
    (image_right_ray_of_boundary_germs hA hB e hzero he
      (SegmentCrossing.right_ne_zero_of_det_ne_zero hab))

/-- Normalized endpoints are transported exactly, in one of two orders. -/
theorem normalized_rays_match_of_boundary_germs
    {A B : Set Plane} {a b c d : Plane}
    (hA : SameBoundaryGerm A (segment ℝ 0 a ∪ segment ℝ 0 b) 0)
    (hB : SameBoundaryGerm B (segment ℝ 0 c ∪ segment ℝ 0 d) 0)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hzero : e 0 = 0) (he : e '' A = B)
    (hab : SegmentCrossing.det a b ≠ 0) :
    (e (‖a‖⁻¹ • a) = ‖c‖⁻¹ • c ∧ e (‖b‖⁻¹ • b) = ‖d‖⁻¹ • d) ∨
      (e (‖a‖⁻¹ • a) = ‖d‖⁻¹ • d ∧ e (‖b‖⁻¹ • b) = ‖c‖⁻¹ • c) :=
  normalized_image_rays_match e hzero hab
    (image_left_ray_of_boundary_germs hA hB e hzero he
      (SegmentCrossing.left_ne_zero_of_det_ne_zero hab))
    (image_right_ray_of_boundary_germs hA hB e hzero he
      (SegmentCrossing.right_ne_zero_of_det_ne_zero hab))

theorem angle_eq_of_boundary_germs
    {A B : Set Plane} {a b c d : Plane}
    (hA : SameBoundaryGerm A (segment ℝ 0 a ∪ segment ℝ 0 b) 0)
    (hB : SameBoundaryGerm B (segment ℝ 0 c ∪ segment ℝ 0 d) 0)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hzero : e 0 = 0) (he : e '' A = B)
    (hab : SegmentCrossing.det a b ≠ 0) : angle a b = angle c d :=
  angle_eq_of_image_rays e hzero hab
    (image_left_ray_of_boundary_germs hA hB e hzero he
      (SegmentCrossing.left_ne_zero_of_det_ne_zero hab))
    (image_right_ray_of_boundary_germs hA hB e hzero he
      (SegmentCrossing.right_ne_zero_of_det_ne_zero hab))

/-- The hypothesis is the congruence of the actual regions.  Its action on
their frontiers is a consequence of being a homeomorphism. -/
theorem normalized_rays_match_of_region_congruence
    {P Q : Set Plane} {a b c d : Plane}
    (hP : SameBoundaryGerm (frontier P) (segment ℝ 0 a ∪ segment ℝ 0 b) 0)
    (hQ : SameBoundaryGerm (frontier Q) (segment ℝ 0 c ∪ segment ℝ 0 d) 0)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hzero : e 0 = 0) (he : e '' P = Q)
    (hab : SegmentCrossing.det a b ≠ 0) :
    (e (‖a‖⁻¹ • a) = ‖c‖⁻¹ • c ∧ e (‖b‖⁻¹ • b) = ‖d‖⁻¹ • d) ∨
      (e (‖a‖⁻¹ • a) = ‖d‖⁻¹ • d ∧ e (‖b‖⁻¹ • b) = ‖c‖⁻¹ • c) :=
  normalized_rays_match_of_boundary_germs hP hQ e hzero
    ((e.toHomeomorph.image_frontier P).trans (congrArg frontier he)) hab

/-- The opening angle of actual two-ray frontier germs is a congruence
invariant.  No polygonality, differentiability, or endpoint matching is assumed. -/
theorem angle_eq_of_region_congruence
    {P Q : Set Plane} {a b c d : Plane}
    (hP : SameBoundaryGerm (frontier P) (segment ℝ 0 a ∪ segment ℝ 0 b) 0)
    (hQ : SameBoundaryGerm (frontier Q) (segment ℝ 0 c ∪ segment ℝ 0 d) 0)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hzero : e 0 = 0) (he : e '' P = Q)
    (hab : SegmentCrossing.det a b ≠ 0) : angle a b = angle c d :=
  angle_eq_of_boundary_germs hP hQ e hzero
    ((e.toHomeomorph.image_frontier P).trans (congrArg frontier he)) hab

end

end Puzzling139335.N6.TripleSectors.Angles.Congruence
