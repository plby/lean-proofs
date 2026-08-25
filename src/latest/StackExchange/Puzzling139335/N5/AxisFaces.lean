import StackExchange.Puzzling139335.Definitions
import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Unit-base images cannot have an axis-aligned top normal

Two points at distance one cannot both have strictly positive coordinates
inside the unit square when their displacement is horizontal or vertical.
The matrix statements below use the actual images of the source base.
-/

namespace Puzzling139335.N5

open PlaneIsometries

private theorem sq_sub_lt_one_of_positive_endpoints {a b u : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ha₁ : a ≤ 1) (hb₁ : b ≤ 1)
    (hu : u = b - a) : u ^ 2 < 1 := by
  have hlo : -1 < u := by linarith
  have hhi : u < 1 := by linarith
  have hprod := mul_pos (sub_pos.mpr hhi) (by linarith : 0 < 1 + u)
  nlinarith only [hprod]

/-- Strict coordinate bounds on the images of a unit base force both
components of its displacement to have squared magnitude less than one. -/
theorem base_column_sq_lt_one_of_positive_endpoints
    (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hA : e 0 ∈ unitSquare) (hB : e (corner 1) ∈ unitSquare)
    (hA₀ : 0 < (e 0) 0) (hA₁ : 0 < (e 0) 1)
    (hB₀ : 0 < e (corner 1) 0) (hB₁ : 0 < e (corner 1) 1) :
    (linearMatrix e 0 0) ^ 2 < 1 ∧ (linearMatrix e 1 0) ^ 2 < 1 := by
  have hcoordinates := affine_apply_eq_matrix_coordinates e (corner 1)
  have hx := congrArg (fun q : Plane => q 0) hcoordinates
  have hy := congrArg (fun q : Plane => q 1) hcoordinates
  simp [corner] at hx hy
  change e (corner 1) 0 = linearMatrix e 0 0 + (e 0) 0 at hx
  change e (corner 1) 1 = linearMatrix e 1 0 + (e 0) 1 at hy
  constructor
  · exact sq_sub_lt_one_of_positive_endpoints hA₀ hB₀ hA.1.2 hB.1.2
      (by linarith only [hx])
  · exact sq_sub_lt_one_of_positive_endpoints hA₁ hB₁ hA.2.2 hB.2.2
      (by linarith only [hy])

/-- An actual placement with both source-base endpoints strictly above the
bottom and to the right of the left side has no axis-aligned top normal. -/
theorem top_row_nonzero_of_positive_unit_base
    (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hA : e 0 ∈ unitSquare) (hB : e (corner 1) ∈ unitSquare)
    (hA₀ : 0 < (e 0) 0) (hA₁ : 0 < (e 0) 1)
    (hB₀ : 0 < e (corner 1) 0) (hB₁ : 0 < e (corner 1) 1) :
    linearMatrix e 1 0 ≠ 0 ∧ linearMatrix e 1 1 ≠ 0 := by
  obtain ⟨hx, hy⟩ := base_column_sq_lt_one_of_positive_endpoints e hA hB
    hA₀ hA₁ hB₀ hB₁
  have hcolumn := linearMatrix_column_dot e 0 0
  have hrow := linearMatrix_row_dot e 1 1
  simp only [ite_true] at hcolumn hrow
  constructor
  · intro hz
    rw [hz] at hcolumn
    nlinarith only [hcolumn, hx]
  · intro hz
    rw [hz] at hrow
    nlinarith only [hrow, hy]

end Puzzling139335.N5
