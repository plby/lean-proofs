import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-! # The two orthogonal matrices with a prescribed second row -/

namespace Puzzling139335.N5.AlignedFace

open PlaneIsometries

/-- An affine isometry's second row fixes its first row up to orientation. -/
theorem linearMatrix_forms_of_second_row (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ}
    (h10 : linearMatrix e 1 0 = c) (h11 : linearMatrix e 1 1 = s) :
    linearMatrix e = !![-s, c; c, s] ∨ linearMatrix e = !![s, -c; c, s] := by
  obtain ⟨a, b, _, hM | hM⟩ := linearMatrix_classification e
  · right
    have ha : a = s := by simpa [hM] using h11
    have hb : b = c := by simpa [hM] using h10
    simpa only [ha, hb] using hM
  · left
    have ha : -a = s := by simpa [hM] using h11
    have ha' : a = -s := by linarith only [ha]
    have hb : b = c := by simpa [hM] using h10
    simpa only [ha', hb, neg_neg] using hM

theorem first_row_forms_of_second_row (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ}
    (h10 : linearMatrix e 1 0 = c) (h11 : linearMatrix e 1 1 = s) :
    (linearMatrix e 0 0 = -s ∧ linearMatrix e 0 1 = c) ∨
      (linearMatrix e 0 0 = s ∧ linearMatrix e 0 1 = -c) := by
  rcases linearMatrix_forms_of_second_row e h10 h11 with hM | hM
  · left
    simp [hM]
  · right
    simp [hM]

theorem second_coordinate_of_second_row (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ}
    (h10 : linearMatrix e 1 0 = c) (h11 : linearMatrix e 1 1 = s) (p : Plane) :
    (e p) 1 = (e 0) 1 + c * p 0 + s * p 1 := by
  rw [affine_apply_eq_matrix_coordinates e p]
  simp [h10, h11]
  ring

/-- The resulting two global affine formulas, including the actual translation. -/
theorem affine_forms_of_second_row (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ}
    (h10 : linearMatrix e 1 0 = c) (h11 : linearMatrix e 1 1 = s) :
    (∀ p : Plane, e p =
      !₂[(e 0) 0 - s * p 0 + c * p 1, (e 0) 1 + c * p 0 + s * p 1]) ∨
    (∀ p : Plane, e p =
      !₂[(e 0) 0 + s * p 0 - c * p 1, (e 0) 1 + c * p 0 + s * p 1]) := by
  rcases linearMatrix_forms_of_second_row e h10 h11 with hM | hM
  · left
    intro p
    rw [affine_apply_eq_matrix_coordinates e p, hM]
    apply plane_ext <;> simp <;> ring
  · right
    intro p
    rw [affine_apply_eq_matrix_coordinates e p, hM]
    apply plane_ext <;> simp <;> ring

end Puzzling139335.N5.AlignedFace
