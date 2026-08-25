import StackExchange.Puzzling139335.CentralRotation.BoundaryCoordinates
import StackExchange.Puzzling139335.CentralRotation.CoordinateCutPairs.CircleHalves

/-!
# The actual cut pairs determined by compatible boundary coordinates

The trace identities in `BoundaryCoordinates` determine all three boundary
curves and their two common endpoints. The cut-pair and endpoint identities
below are conclusions, rather than additional conditions on the coordinate
data.
-/

open Set Schoenflies

namespace Puzzling139335.CentralRotation.BoundaryCoordinates

variable {M Γ N : Set Plane} (d : BoundaryCoordinates M Γ N)

/-- The cut begins at the same half-period point in both tile parametrizations. -/
theorem right_half_eq_left_half :
    circleParam d.rightParam (1 / 2) = circleParam d.leftParam (1 / 2) := by
  have h := d.cutAgree (1 / 2) (by norm_num)
  simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using h.symm

/-- Reversing the cut identifies the right loop's zero point with the left
loop's end-of-period point. -/
theorem right_zero_eq_left_one :
    circleParam d.rightParam 0 = circleParam d.leftParam 1 := by
  simpa only [sub_self] using (d.cutAgree 1 (by norm_num)).symm

/-- Periodicity identifies the other pair of cut endpoints. -/
theorem right_one_eq_left_one :
    circleParam d.rightParam 1 = circleParam d.leftParam 1 :=
  (circleParam_zero_eq_one d.rightParam).symm.trans d.right_zero_eq_left_one

/-- The half-period cut point also lies at the same parameter on the outer loop. -/
theorem outer_half_eq_left_half :
    circleParam d.outerParam (1 / 2) = circleParam d.leftParam (1 / 2) :=
  (d.outerLeftAgree (by norm_num)).symm

/-- The end-of-period cut point agrees on the outer and left loops. -/
theorem outer_one_eq_left_one :
    circleParam d.outerParam 1 = circleParam d.leftParam 1 :=
  (d.outerRightAgree (by norm_num)).symm.trans d.right_one_eq_left_one

/-- The same common endpoint is the zero point of the outer loop. -/
theorem outer_zero_eq_left_one :
    circleParam d.outerParam 0 = circleParam d.leftParam 1 :=
  (circleParam_zero_eq_one d.outerParam).trans d.outer_one_eq_left_one

/-- The two coordinate cut endpoints are distinct, by circle injectivity. -/
theorem sourceEndpoints_ne :
    circleParam d.leftParam (1 / 2) ≠ circleParam d.leftParam 1 := by
  intro heq
  have hparam := circleParam_injOn_Icc d.leftInjective
    (a := (1 / 2 : ℝ)) (b := 1) (by norm_num)
    (show (1 / 2 : ℝ) ∈ Icc (1 / 2 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (1 / 2 : ℝ) 1 by norm_num) heq
  norm_num at hparam

/-- The first half of the right loop is exactly the same actual cut, traversed
in the opposite direction from the left loop's second half. -/
theorem rightCutImage : circleParam d.rightParam '' Icc (0 : ℝ) (1 / 2) = Γ := by
  refine Eq.trans ?_ d.leftCutImage
  apply Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    have hs : 1 - t ∈ Icc (1 / 2 : ℝ) 1 :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    refine ⟨1 - t, hs, ?_⟩
    simpa only [show (1 : ℝ) - (1 - t) = t by ring] using d.cutAgree (1 - t) hs
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    exact (d.cutAgree t ht).symm

/-- The first half of the outer loop traces the actual left outer arc. -/
theorem outerLeftImage : circleParam d.outerParam '' Icc (0 : ℝ) (1 / 2) = M := by
  calc
    circleParam d.outerParam '' Icc (0 : ℝ) (1 / 2) =
        circleParam d.leftParam '' Icc (0 : ℝ) (1 / 2) :=
      image_congr fun t ht => (d.outerLeftAgree ht).symm
    _ = M := d.leftOuterImage

/-- The second half of the outer loop traces the actual right outer arc. -/
theorem outerRightImage : circleParam d.outerParam '' Icc (1 / 2 : ℝ) 1 = N := by
  calc
    circleParam d.outerParam '' Icc (1 / 2 : ℝ) 1 =
        circleParam d.rightParam '' Icc (1 / 2 : ℝ) 1 :=
      image_congr fun t ht => (d.outerRightAgree ht).symm
    _ = N := d.rightOuterImage

/-- The left tile boundary is split by the actual cut and left outer arc at
the two coordinate endpoints. -/
theorem leftCutPair :
    IsCutPair (range d.leftParam)
      (circleParam d.leftParam (1 / 2)) (circleParam d.leftParam 1) Γ M := by
  simpa only [d.leftCutImage, d.leftOuterImage] using
    isCutPair_circle_halves d.leftContinuous d.leftInjective

/-- The right tile boundary has the same two cut endpoints and the actual
cut/right-outer-arc splitting. -/
theorem rightCutPair :
    IsCutPair (range d.rightParam)
      (circleParam d.leftParam (1 / 2)) (circleParam d.leftParam 1) Γ N := by
  simpa only [d.rightOuterImage, d.rightCutImage,
    d.right_half_eq_left_half, d.right_one_eq_left_one] using
    (isCutPair_circle_halves d.rightContinuous d.rightInjective).symm

/-- The outer boundary is split into the actual left and right outer arcs,
with the same two coordinate endpoints as the shared cut. -/
theorem outerCutPair :
    IsCutPair (range d.outerParam)
      (circleParam d.leftParam (1 / 2)) (circleParam d.leftParam 1) M N := by
  simpa only [d.outerLeftImage, d.outerRightImage,
    d.outer_half_eq_left_half, d.outer_one_eq_left_one] using
    (isCutPair_circle_halves d.outerContinuous d.outerInjective).symm

theorem left_range_eq : range d.leftParam = M ∪ Γ :=
  d.leftCutPair.union_eq.symm.trans (union_comm Γ M)

theorem right_range_eq : range d.rightParam = N ∪ Γ :=
  d.rightCutPair.union_eq.symm.trans (union_comm Γ N)

theorem outer_range_eq : range d.outerParam = M ∪ N :=
  d.outerCutPair.union_eq.symm

end Puzzling139335.CentralRotation.BoundaryCoordinates
