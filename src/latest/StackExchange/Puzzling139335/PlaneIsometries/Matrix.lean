import StackExchange.Puzzling139335.PlaneIsometries

/-!
# Matrix consequences of the plane-isometry classification
-/

namespace Puzzling139335.PlaneIsometries

noncomputable section

/-- Each matrix column is the image displacement of a coordinate unit vector. -/
theorem linearMatrix_apply_eq_sub (e : Plane ≃ᵃⁱ[ℝ] Plane) (i j : Fin 2) :
    linearMatrix e i j = e (EuclideanSpace.single j 1) i - (e 0) i := by
  exact eq_sub_of_add_eq
    (congrArg (fun p : Plane => p i)
      (affine_apply_eq_linear_add e (EuclideanSpace.single j 1))).symm

/-- An affine isometry is evaluated by its linear matrix and translation. -/
theorem affine_apply_eq_matrix_coordinates (e : Plane ≃ᵃⁱ[ℝ] Plane) (p : Plane) :
    e p = !₂[
      linearMatrix e 0 0 * p 0 + linearMatrix e 0 1 * p 1 + (e 0) 0,
      linearMatrix e 1 0 * p 0 + linearMatrix e 1 1 * p 1 + (e 0) 1] := by
  have hp : p = p 0 • EuclideanSpace.single 0 (1 : ℝ) +
      p 1 • EuclideanSpace.single 1 (1 : ℝ) := by
    apply plane_ext <;> simp
  have hL : e.linearIsometryEquiv p =
      p 0 • e.linearIsometryEquiv (EuclideanSpace.single 0 1) +
      p 1 • e.linearIsometryEquiv (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [hp]
    simp
  rw [affine_apply_eq_linear_add, hL]
  apply plane_ext <;> simp [linearMatrix, mul_comm]

/-- The origin and the two coordinate unit vectors determine an affine
isometry of the plane. -/
theorem affine_eq_of_origin_basis {e f : Plane ≃ᵃⁱ[ℝ] Plane}
    (h₀ : e 0 = f 0)
    (hb : ∀ j : Fin 2, e (EuclideanSpace.single j 1) = f (EuclideanSpace.single j 1)) :
    e = f := by
  have hm : linearMatrix e = linearMatrix f := by
    ext i j
    rw [linearMatrix_apply_eq_sub, linearMatrix_apply_eq_sub, hb j, h₀]
  apply AffineIsometryEquiv.ext
  intro p
  rw [affine_apply_eq_matrix_coordinates e p, affine_apply_eq_matrix_coordinates f p, hm, h₀]

/-- Explicit orthonormality of any pair of matrix columns. -/
theorem linearMatrix_column_dot (e : Plane ≃ᵃⁱ[ℝ] Plane) (j k : Fin 2) :
    linearMatrix e 0 j * linearMatrix e 0 k +
      linearMatrix e 1 j * linearMatrix e 1 k = if j = k then 1 else 0 := by
  obtain ⟨c, s, hcs, he | he⟩ := linearMatrix_classification e
  · rw [he]
    fin_cases j <;> fin_cases k <;> simp <;> nlinarith [hcs]
  · rw [he]
    fin_cases j <;> fin_cases k <;> simp <;> nlinarith [hcs]

/-- Explicit orthonormality of any pair of matrix rows. -/
theorem linearMatrix_row_dot (e : Plane ≃ᵃⁱ[ℝ] Plane) (i j : Fin 2) :
    linearMatrix e i 0 * linearMatrix e j 0 +
      linearMatrix e i 1 * linearMatrix e j 1 = if i = j then 1 else 0 := by
  obtain ⟨c, s, hcs, he | he⟩ := linearMatrix_classification e
  · rw [he]
    fin_cases i <;> fin_cases j <;> simp <;> nlinarith [hcs]
  · rw [he]
    fin_cases i <;> fin_cases j <;> simp <;> nlinarith [hcs]

/-- The matrix determinant records one of the two possible orientations. -/
theorem linearMatrix_det_eq_one_or_neg_one (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (linearMatrix e).det = 1 ∨ (linearMatrix e).det = -1 := by
  obtain ⟨c, s, hcs, he | he⟩ := linearMatrix_classification e
  · left
    rw [he, Matrix.det_fin_two]
    simp
    nlinarith [hcs]
  · right
    rw [he, Matrix.det_fin_two]
    simp
    nlinarith [hcs]

/-- Hence the linear matrix is nonsingular. -/
theorem linearMatrix_det_ne_zero (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (linearMatrix e).det ≠ 0 := by
  rcases linearMatrix_det_eq_one_or_neg_one e with h | h <;> simp [h]

end

end Puzzling139335.PlaneIsometries
