import StackExchange.Puzzling139335.RectangularHull.RotationFit
import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Four rectangle corners force an axis-aligned affine isometry

The coordinate extrema of the four corners give the two bounding-box widths.
The matrix classification includes both orientations of a plane isometry.
-/

namespace Puzzling139335.RectangularHull

open Set PlaneIsometries

/-- Four affine corner coordinates in the unit interval bound the sum of
the absolute values of the two edge contributions. -/
theorem four_corners_width_le_one {t a b : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hta : t + a ∈ Icc (0 : ℝ) 1)
    (htb : t + b ∈ Icc (0 : ℝ) 1) (htab : t + a + b ∈ Icc (0 : ℝ) 1) :
    |a| + |b| ≤ 1 := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]
    linarith only [ht.1, htab.2]
  · rw [abs_of_nonneg ha, abs_of_nonpos hb]
    linarith only [hta.2, htb.1]
  · rw [abs_of_nonpos ha, abs_of_nonneg hb]
    linarith only [hta.1, htb.2]
  · rw [abs_of_nonpos ha, abs_of_nonpos hb]
    linarith only [ht.2, htab.1]

private theorem affine_coordinate_apply (e : Plane ≃ᵃⁱ[ℝ] Plane) (p : Plane)
    (i : Fin 2) :
    (e p) i = linearMatrix e i 0 * p 0 + linearMatrix e i 1 * p 1 + (e 0) i := by
  have he := congrArg (fun q : Plane => q i) (affine_apply_eq_matrix_coordinates e p)
  fin_cases i <;> simpa using he

/-- The four image corners bound either coordinate width of the affine image. -/
theorem matrix_row_width_le_one_of_corners (e : Plane ≃ᵃⁱ[ℝ] Plane) (i : Fin 2)
    {h : ℝ} (hh0 : 0 ≤ h)
    (h00 : e !₂[0, 0] ∈ unitSquare) (h10 : e !₂[1, 0] ∈ unitSquare)
    (h0h : e !₂[0, h] ∈ unitSquare) (h1h : e !₂[1, h] ∈ unitSquare) :
    |linearMatrix e i 0| + h * |linearMatrix e i 1| ≤ 1 := by
  have hcoord (p : Plane) (hp : e p ∈ unitSquare) :
      linearMatrix e i 0 * p 0 + linearMatrix e i 1 * p 1 + (e 0) i ∈
        Icc (0 : ℝ) 1 := by
    rw [← affine_coordinate_apply e p i]
    fin_cases i
    · exact hp.1
    · exact hp.2
  have hfit : |linearMatrix e i 0| + |h * linearMatrix e i 1| ≤ 1 := by
    apply four_corners_width_le_one (t := (e 0) i)
    · simpa using hcoord !₂[0, 0] h00
    · simpa [add_comm] using hcoord !₂[1, 0] h10
    · simpa [mul_comm, add_comm] using hcoord !₂[0, h] h0h
    · simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hcoord !₂[1, h] h1h
  simpa only [abs_mul, abs_of_nonneg hh0] using hfit

/-- Any affine isometry fitting the four corners of a `1 × h` rectangle into
the unit square, with `h ≥ 1/2`, has an axis-aligned linear part. -/
theorem affine_rectangle_fit_axis_aligned (e : Plane ≃ᵃⁱ[ℝ] Plane) {h : ℝ}
    (hh : 1 / 2 ≤ h)
    (h00 : e !₂[0, 0] ∈ unitSquare) (h10 : e !₂[1, 0] ∈ unitSquare)
    (h0h : e !₂[0, h] ∈ unitSquare) (h1h : e !₂[1, h] ∈ unitSquare) :
    linearMatrix e 0 0 = 0 ∨ linearMatrix e 1 0 = 0 := by
  have hh0 : 0 ≤ h := by linarith
  have hw := matrix_row_width_le_one_of_corners e 0 hh0 h00 h10 h0h h1h
  have ht := matrix_row_width_le_one_of_corners e 1 hh0 h00 h10 h0h h1h
  obtain ⟨c, s, hcs, he | he⟩ := linearMatrix_classification e
  all_goals
    have hw' : |c| + h * |s| ≤ 1 := by simpa [he] using hw
    have ht' : |s| + h * |c| ≤ 1 := by simpa [he] using ht
    simpa [he] using rotation_fit_axis_aligned hcs hh hw' ht'

end Puzzling139335.RectangularHull
