import StackExchange.Puzzling139335.PlaneIsometries.Matrix
import StackExchange.Puzzling139335.SquareSymmetry.Basic

/-!
# Normalizing a reflection at a square corner

The linear matrix records composition in the order used by affine
isometries.  In particular, conjugation by a coordinate reflection does
not change orientation.  No geometric classification hypothesis is used
in proving that an orientation-reversing isometry with a fixed point is
an involution.
-/

namespace Puzzling139335

noncomputable section

namespace PlaneIsometries

/-- The matrix of composition is the product, in evaluation order. -/
theorem linearMatrix_trans (e f : Plane ≃ᵃⁱ[ℝ] Plane) :
    linearMatrix (e.trans f) = linearMatrix f * linearMatrix e := by
  have hdecomp (p : Plane) : p =
      p 0 • EuclideanSpace.single 0 (1 : ℝ) +
      p 1 • EuclideanSpace.single 1 (1 : ℝ) := by
    apply plane_ext <;> simp
  ext i j
  change f.linearIsometryEquiv
      (e.linearIsometryEquiv (EuclideanSpace.single j 1)) i = _
  rw [hdecomp (e.linearIsometryEquiv (EuclideanSpace.single j 1))]
  simp [Matrix.mul_apply, Fin.sum_univ_two, linearMatrix, mul_comm]

/-- Determinants multiply under composition. -/
theorem linearMatrix_det_trans (e f : Plane ≃ᵃⁱ[ℝ] Plane) :
    (linearMatrix (e.trans f)).det = (linearMatrix f).det * (linearMatrix e).det := by
  rw [linearMatrix_trans, Matrix.det_mul]

/-- Applying the same affine isometry on either side preserves the
orientation of the middle isometry. -/
theorem linearMatrix_det_double_trans (e f : Plane ≃ᵃⁱ[ℝ] Plane) :
    (linearMatrix ((f.trans e).trans f)).det = (linearMatrix e).det := by
  rw [linearMatrix_det_trans, linearMatrix_det_trans]
  rcases linearMatrix_det_eq_one_or_neg_one f with hf | hf <;> simp [hf]

/-- The reversing coordinate form fixing the origin is an involution. -/
theorem involutive_of_reversing_coordinates (e : Plane ≃ᵃⁱ[ℝ] Plane)
    {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (he0 : e 0 = 0)
    (hform : ∀ p, e p = reversingCoordinates c s (e 0) p) :
    Function.Involutive e := by
  intro p
  rw [hform (e p), hform p, he0]
  apply plane_ext
  · simp only [reversingCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, add_zero]
    linear_combination p 0 * hcs
  · simp only [reversingCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      PiLp.zero_apply, add_zero]
    linear_combination p 1 * hcs

/-- An orientation-reversing plane isometry that fixes a point is an
involution, including when its fixed point is not the origin. -/
theorem involutive_of_det_neg_one_of_fixed_point (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hdet : (linearMatrix e).det = -1) {q : Plane} (hq : e q = q) :
    Function.Involutive e := by
  obtain ⟨c, s, hcs, hm | hm⟩ := linearMatrix_classification e
  · rw [hm, Matrix.det_fin_two] at hdet
    simp at hdet
    nlinarith [hcs]
  · have he (p : Plane) :
        e p = !₂[c * p 0 + s * p 1 + (e 0) 0,
          s * p 0 - c * p 1 + (e 0) 1] := by
      rw [affine_apply_eq_matrix_coordinates, hm]
      apply plane_ext <;> simp <;> ring
    have hq₀ := congrArg (fun p : Plane => p 0) hq
    have hq₁ := congrArg (fun p : Plane => p 1) hq
    rw [he q] at hq₀ hq₁
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hq₀ hq₁
    have ht₀ : (e 0) 0 = q 0 - c * q 0 - s * q 1 := by linarith
    have ht₁ : (e 0) 1 = q 1 - s * q 0 + c * q 1 := by linarith
    intro p
    rw [he (e p), he p]
    apply plane_ext
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ht₀, ht₁]
      linear_combination (p 0 - q 0) * hcs
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ht₀, ht₁]
      linear_combination (p 1 - q 1) * hcs

end PlaneIsometries

namespace DoubleCorner.Reflection

/-- Conjugation by the coordinate reflection at a square corner preserves
the determinant of the linear part. -/
theorem cornerFlip_conjugate_det (v : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (PlaneIsometries.linearMatrix
      (((SquareSymmetry.cornerFlip v).trans e).trans (SquareSymmetry.cornerFlip v))).det =
      (PlaneIsometries.linearMatrix e).det :=
  PlaneIsometries.linearMatrix_det_double_trans e (SquareSymmetry.cornerFlip v)

/-- A fixed square corner becomes a fixed origin after coordinate
reflection. -/
theorem cornerFlip_conjugate_zero (v : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hfix : e (corner v) = corner v) :
    (((SquareSymmetry.cornerFlip v).trans e).trans (SquareSymmetry.cornerFlip v)) 0 = 0 := by
  change SquareSymmetry.cornerFlip v (e (SquareSymmetry.cornerFlip v 0)) = 0
  rw [SquareSymmetry.cornerFlip_zero, hfix, SquareSymmetry.cornerFlip_corner]

/-- The normalized isometry is again an orientation-reversing isometry
fixing the origin. -/
theorem cornerFlip_conjugate_reflection (v : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hdet : (PlaneIsometries.linearMatrix e).det = -1)
    (hfix : e (corner v) = corner v) :
    (PlaneIsometries.linearMatrix
      (((SquareSymmetry.cornerFlip v).trans e).trans (SquareSymmetry.cornerFlip v))).det = -1 ∧
      (((SquareSymmetry.cornerFlip v).trans e).trans (SquareSymmetry.cornerFlip v)) 0 = 0 :=
  ⟨(cornerFlip_conjugate_det v e).trans hdet, cornerFlip_conjugate_zero v e hfix⟩

end DoubleCorner.Reflection

end

end Puzzling139335
