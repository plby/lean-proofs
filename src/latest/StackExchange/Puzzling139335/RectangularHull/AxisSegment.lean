import StackExchange.Puzzling139335.PlaneIsometries.Matrix
import StackExchange.Puzzling139335.SquareGeometry.Scalar

/-!
# The image of an axis-aligned unit base spans the square

The two image endpoints lie on opposite ends of a horizontal or vertical
unit segment.  Affine preservation of segments then gives the actual image
set, including when the endpoint order is reversed.
-/

namespace Puzzling139335.RectangularHull

open Set PlaneIsometries

theorem affine_unit_base_coordinate_difference (e : Plane ≃ᵃⁱ[ℝ] Plane) (i : Fin 2) :
    (e !₂[1, 0]) i - (e !₂[0, 0]) i = linearMatrix e i 0 := by
  rw [affine_apply_eq_matrix_coordinates e !₂[1, 0],
    affine_apply_eq_matrix_coordinates e !₂[0, 0]]
  fin_cases i <;> simp

private theorem vertical_segment_eq_of_unit_difference {p q : Plane}
    (hp : p 1 ∈ Icc (0 : ℝ) 1) (hq : q 1 ∈ Icc (0 : ℝ) 1)
    (hzero : p 0 = q 0) (hlen : (p 1 - q 1) ^ 2 = 1) :
    segment ℝ p q = segment ℝ !₂[p 0, 0] !₂[p 0, 1] := by
  rcases endpoints_of_mem_Icc_of_sub_sq_eq_one hp hq hlen with
    ⟨hp0, hq1⟩ | ⟨hp1, hq0⟩
  · have hep : p = !₂[p 0, 0] := plane_ext rfl hp0
    have heq : q = !₂[p 0, 1] := plane_ext hzero.symm hq1
    exact congrArg₂ (segment ℝ) hep heq
  · have hep : p = !₂[p 0, 1] := plane_ext rfl hp1
    have heq : q = !₂[p 0, 0] := plane_ext hzero.symm hq0
    exact (congrArg₂ (segment ℝ) hep heq).trans (segment_symm ℝ _ _)

private theorem horizontal_segment_eq_of_unit_difference {p q : Plane}
    (hp : p 0 ∈ Icc (0 : ℝ) 1) (hq : q 0 ∈ Icc (0 : ℝ) 1)
    (hone : p 1 = q 1) (hlen : (p 0 - q 0) ^ 2 = 1) :
    segment ℝ p q = segment ℝ !₂[0, p 1] !₂[1, p 1] := by
  rcases endpoints_of_mem_Icc_of_sub_sq_eq_one hp hq hlen with
    ⟨hp0, hq1⟩ | ⟨hp1, hq0⟩
  · have hep : p = !₂[0, p 1] := plane_ext hp0 rfl
    have heq : q = !₂[1, p 1] := plane_ext hq1 hone.symm
    exact congrArg₂ (segment ℝ) hep heq
  · have hep : p = !₂[1, p 1] := plane_ext hp1 rfl
    have heq : q = !₂[0, p 1] := plane_ext hq0 hone.symm
    exact (congrArg₂ (segment ℝ) hep heq).trans (segment_symm ℝ _ _)

/-- Row and column tests for axis alignment agree for a plane isometry. -/
theorem matrix_row_axis_iff_column_axis (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (linearMatrix e 0 0 = 0 ∨ linearMatrix e 0 1 = 0) ↔
      (linearMatrix e 0 0 = 0 ∨ linearMatrix e 1 0 = 0) := by
  obtain ⟨c, s, _hcs, he | he⟩ := linearMatrix_classification e
  all_goals simp [he]

/-- The actual image of the unit base is a full vertical or horizontal
unit segment when the first matrix column is axis aligned. -/
theorem affine_unit_base_image_axis_segment (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (h0 : e !₂[0, 0] ∈ unitSquare) (h1 : e !₂[1, 0] ∈ unitSquare)
    (hAxis : linearMatrix e 0 0 = 0 ∨ linearMatrix e 1 0 = 0) :
    (∃ x ∈ Icc (0 : ℝ) 1,
      e '' segment ℝ !₂[0, 0] !₂[1, 0] = segment ℝ !₂[x, 0] !₂[x, 1]) ∨
    (∃ y ∈ Icc (0 : ℝ) 1,
      e '' segment ℝ !₂[0, 0] !₂[1, 0] = segment ℝ !₂[0, y] !₂[1, y]) := by
  have hdiff0 := affine_unit_base_coordinate_difference e 0
  have hdiff1 := affine_unit_base_coordinate_difference e 1
  have hunit : linearMatrix e 0 0 ^ 2 + linearMatrix e 1 0 ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_column_dot e 0 0
  have himage : e '' segment ℝ !₂[0, 0] !₂[1, 0] =
      segment ℝ (e !₂[0, 0]) (e !₂[1, 0]) :=
    image_segment ℝ e.toAffineEquiv.toAffineMap _ _
  rcases hAxis with hAxis | hAxis
  · left
    refine ⟨(e !₂[0, 0]) 0, h0.1, ?_⟩
    have hzero : (e !₂[0, 0]) 0 = (e !₂[1, 0]) 0 := by
      linarith only [hdiff0, hAxis]
    have hlen : ((e !₂[0, 0]) 1 - (e !₂[1, 0]) 1) ^ 2 = 1 := by
      rw [sub_sq_comm, hdiff1]
      simpa [hAxis] using hunit
    exact himage.trans (vertical_segment_eq_of_unit_difference
      (p := e !₂[0, 0]) (q := e !₂[1, 0]) h0.2 h1.2 hzero hlen)
  · right
    refine ⟨(e !₂[0, 0]) 1, h0.2, ?_⟩
    have hone : (e !₂[0, 0]) 1 = (e !₂[1, 0]) 1 := by
      linarith only [hdiff1, hAxis]
    have hlen : ((e !₂[0, 0]) 0 - (e !₂[1, 0]) 0) ^ 2 = 1 := by
      rw [sub_sq_comm, hdiff0]
      simpa [hAxis] using hunit
    exact himage.trans (horizontal_segment_eq_of_unit_difference
      (p := e !₂[0, 0]) (q := e !₂[1, 0]) h0.1 h1.1 hone hlen)

/-- The row-axis formulation is the one supplied by the side-gap coverage
argument. -/
theorem affine_unit_base_image_axis_segment_of_row_axis (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (h0 : e !₂[0, 0] ∈ unitSquare) (h1 : e !₂[1, 0] ∈ unitSquare)
    (hAxis : linearMatrix e 0 0 = 0 ∨ linearMatrix e 0 1 = 0) :
    (∃ x ∈ Icc (0 : ℝ) 1,
      e '' segment ℝ !₂[0, 0] !₂[1, 0] = segment ℝ !₂[x, 0] !₂[x, 1]) ∨
    (∃ y ∈ Icc (0 : ℝ) 1,
      e '' segment ℝ !₂[0, 0] !₂[1, 0] = segment ℝ !₂[0, y] !₂[1, y]) :=
  affine_unit_base_image_axis_segment e h0 h1 ((matrix_row_axis_iff_column_axis e).mp hAxis)

end Puzzling139335.RectangularHull
