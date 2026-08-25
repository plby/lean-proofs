import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Transporting a vertical image span to source coordinates

The linear matrix of a plane isometry has determinant one or minus one.
If two image points have equal horizontal coordinate, their source
vertical displacement is therefore, up to sign, the image vertical
displacement times the upper-left matrix entry.
-/

namespace Puzzling139335.N4HalfLeg

open PlaneIsometries

/-- A vertical image displacement determines the source vertical
displacement, with the sign recording the isometry's orientation. -/
theorem vertical_span_or_neg_of_vertical_image (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (p q : Plane) (hvertical : (e p) 0 = (e q) 0) :
    q 1 - p 1 = linearMatrix e 0 0 * ((e q) 1 - (e p) 1) ∨
      p 1 - q 1 = linearMatrix e 0 0 * ((e q) 1 - (e p) 1) := by
  have hp := affine_apply_eq_matrix_coordinates e p
  have hq := affine_apply_eq_matrix_coordinates e q
  obtain ⟨c, s, hcs, he | he⟩ := linearMatrix_classification e
  · left
    simp [hp, hq, he] at hvertical ⊢
    linear_combination s * hvertical - (q 1 - p 1) * hcs
  · right
    simp [hp, hq, he] at hvertical ⊢
    linear_combination s * hvertical + (q 1 - p 1) * hcs

/-- The preimages of two contacts on the right square side have one of
the two source height orders supplied by the matrix transport identity. -/
theorem vertical_span_or_neg_of_right_preimages (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (bottom top : ℝ) :
    (e.symm !₂[1, top]) 1 - (e.symm !₂[1, bottom]) 1 =
        linearMatrix e 0 0 * (top - bottom) ∨
      (e.symm !₂[1, bottom]) 1 - (e.symm !₂[1, top]) 1 =
        linearMatrix e 0 0 * (top - bottom) := by
  simpa using vertical_span_or_neg_of_vertical_image e
    (e.symm !₂[1, bottom]) (e.symm !₂[1, top]) (by simp)

end Puzzling139335.N4HalfLeg
