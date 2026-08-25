import StackExchange.Puzzling139335.RectangularHull.AxisSegment
import StackExchange.Puzzling139335.BandMass.Geometry

/-!
# Height bounds for images with a horizontal unit base

When the horizontal source direction has zero vertical image component,
orthogonality makes the remaining vertical matrix entry equal to `1` or
`-1`.  Therefore the image height depends only on the source height.  The
pointwise bound below makes no assumption on the horizontal coordinate,
on a convex hull, or on regularity of a source set.
-/

open Set

namespace Puzzling139335.N4OuterPair

open PlaneIsometries

/-- A horizontal image of the source base leaves vertical scale `±1`. -/
theorem horizontal_vertical_coefficient (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hAxis : linearMatrix e 1 0 = 0) :
    linearMatrix e 1 1 = 1 ∨ linearMatrix e 1 1 = -1 := by
  have hsq : linearMatrix e 1 1 ^ 2 = 1 := by
    simpa [hAxis, pow_two] using linearMatrix_row_dot e 1 1
  exact sq_eq_one_iff.mp hsq

/-- The image height is independent of the horizontal source coordinate. -/
theorem horizontal_apply_y (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hAxis : linearMatrix e 1 0 = 0) (p : Plane) :
    (e p) 1 = linearMatrix e 1 1 * p 1 + (e !₂[0, 0]) 1 := by
  have horigin : (!₂[0, 0] : Plane) = 0 := by
    apply plane_ext <;> rfl
  simpa [hAxis, horigin] using
    congrArg (fun q : Plane => q 1) (affine_apply_eq_matrix_coordinates e p)

/-- Source heights between zero and `h` give a band of radius `h` about
the image base height, with no horizontal-coordinate assumption. -/
theorem horizontal_point_band_bounds (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hAxis : linearMatrix e 1 0 = 0) {h : ℝ} {p : Plane}
    (hp0 : 0 ≤ p 1) (hph : p 1 ≤ h) :
    (e !₂[0, 0]) 1 - h ≤ (e p) 1 ∧
      (e p) 1 ≤ (e !₂[0, 0]) 1 + h := by
  rw [horizontal_apply_y e hAxis p]
  rcases horizontal_vertical_coefficient e hAxis with hpos | hneg
  · rw [hpos, one_mul]
    constructor <;> linarith only [hp0, hph]
  · rw [hneg, neg_one_mul]
    constructor <;> linarith only [hp0, hph]

/-- Set membership in an image of a horizontal source band gives the same
height bounds; image containment in the unit square is not required. -/
theorem horizontal_image_band_bounds (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hAxis : linearMatrix e 1 0 = 0) {h : ℝ} {P : Set Plane}
    (hP : P ⊆ horizontalBand 0 h) {p : Plane} (hp : p ∈ e '' P) :
    (e !₂[0, 0]) 1 - h ≤ p 1 ∧ p 1 ≤ (e !₂[0, 0]) 1 + h := by
  obtain ⟨q, hq, rfl⟩ := hp
  exact horizontal_point_band_bounds e hAxis (hP hq).2.1 (hP hq).2.2

/-- If the image also fits the square, the height bound is a literal
containment in a horizontal band of width one. -/
theorem horizontal_image_subset_band (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hAxis : linearMatrix e 1 0 = 0) {h : ℝ} {P : Set Plane}
    (hP : P ⊆ horizontalBand 0 h) (hfit : MapsTo e P unitSquare) :
    e '' P ⊆ horizontalBand ((e !₂[0, 0]) 1 - h) ((e !₂[0, 0]) 1 + h) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact ⟨(hfit hq).1, horizontal_point_band_bounds e hAxis (hP hq).2.1 (hP hq).2.2⟩

/-- A horizontal image of the actual unit base spans the full square
width, even when the isometry reverses the endpoint order. -/
theorem horizontal_unit_base_image (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (h0 : e !₂[0, 0] ∈ unitSquare) (h1 : e !₂[1, 0] ∈ unitSquare)
    (hAxis : linearMatrix e 1 0 = 0) :
    e '' segment ℝ !₂[0, 0] !₂[1, 0] =
      segment ℝ !₂[0, (e !₂[0, 0]) 1] !₂[1, (e !₂[0, 0]) 1] := by
  have hdiff0 := RectangularHull.affine_unit_base_coordinate_difference e 0
  have hdiff1 := RectangularHull.affine_unit_base_coordinate_difference e 1
  have hunit : linearMatrix e 0 0 ^ 2 + linearMatrix e 1 0 ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_column_dot e 0 0
  have hone : (e !₂[0, 0]) 1 = (e !₂[1, 0]) 1 := by
    linarith only [hdiff1, hAxis]
  have hlen : ((e !₂[0, 0]) 0 - (e !₂[1, 0]) 0) ^ 2 = 1 := by
    rw [sub_sq_comm, hdiff0]
    simpa [hAxis] using hunit
  have himage : e '' segment ℝ !₂[0, 0] !₂[1, 0] =
      segment ℝ (e !₂[0, 0]) (e !₂[1, 0]) :=
    image_segment ℝ e.toAffineEquiv.toAffineMap _ _
  rw [himage]
  rcases endpoints_of_mem_Icc_of_sub_sq_eq_one h0.1 h1.1 hlen with
    ⟨hp0, hq1⟩ | ⟨hp1, hq0⟩
  · have hep : e !₂[0, 0] = !₂[0, (e !₂[0, 0]) 1] := plane_ext hp0 rfl
    have heq : e !₂[1, 0] = !₂[1, (e !₂[0, 0]) 1] := plane_ext hq1 hone.symm
    exact congrArg₂ (segment ℝ) hep heq
  · have hep : e !₂[0, 0] = !₂[1, (e !₂[0, 0]) 1] := plane_ext hp1 rfl
    have heq : e !₂[1, 0] = !₂[0, (e !₂[0, 0]) 1] := plane_ext hq0 hone.symm
    exact (congrArg₂ (segment ℝ) hep heq).trans (segment_symm ℝ _ _)

end Puzzling139335.N4OuterPair
