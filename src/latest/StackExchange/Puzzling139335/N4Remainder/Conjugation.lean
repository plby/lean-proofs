import StackExchange.Puzzling139335.DoubleCorner.Reflection.Conjugation
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Transporting intrinsic reflection symmetries

Conjugation by an arbitrary plane isometry preserves the determinant of
the linear part.  Thus a horizontal-reflection symmetry of any congruent
copy transports to an orientation-reversing symmetry of the prototype.
-/

open Set

namespace Puzzling139335.N4Remainder

open PlaneIsometries

/-- The determinant of an inverse is the reciprocal determinant. -/
theorem inverse_det_mul_det (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (linearMatrix e.symm).det * (linearMatrix e).det = 1 := by
  have he : e.trans e.symm = AffineIsometryEquiv.refl ℝ Plane := by
    ext x
    simp
  have hm : linearMatrix (AffineIsometryEquiv.refl ℝ Plane) = 1 := by
    ext i j
    rw [linearMatrix_apply_eq_sub]
    simp [Matrix.one_apply]
  rw [← linearMatrix_det_trans, he, hm, Matrix.det_one]

/-- The orientation of an affine isometry is unchanged by conjugation. -/
theorem conjugate_det (e g : Plane ≃ᵃⁱ[ℝ] Plane) :
    (linearMatrix ((e.trans g).trans e.symm)).det = (linearMatrix g).det := by
  rw [linearMatrix_det_trans, linearMatrix_det_trans]
  calc
    (linearMatrix e.symm).det * ((linearMatrix g).det * (linearMatrix e).det) =
        (linearMatrix g).det * ((linearMatrix e.symm).det * (linearMatrix e).det) := by
      ring
    _ = (linearMatrix g).det := by rw [inverse_det_mul_det]; ring

/-- Conjugation transports an actual symmetry of a congruent image back
to the original set. -/
theorem conjugate_image_eq {P Q : Set Plane} (e g : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' P = Q) (hg : g '' Q = Q) :
    ((e.trans g).trans e.symm) '' P = P := by
  have hcomp : ((e.trans g).trans e.symm) '' P = e.symm '' (g '' (e '' P)) := by
    simp only [Set.image_image]
    rfl
  rw [hcomp, he, hg, ← he]
  rw [Set.image_image]
  change (fun x => e.symm (e x)) '' P = P
  simp only [AffineIsometryEquiv.symm_apply_apply, image_id']

/-- The concrete horizontal midline reflection reverses orientation. -/
theorem horizontal_det :
    (linearMatrix ReflectionSeparation.horizontal).det = -1 := by
  have hm : linearMatrix ReflectionSeparation.horizontal = !![1, 0; 0, -1] := by
    ext i j
    rw [linearMatrix_apply_eq_sub]
    fin_cases i <;> fin_cases j <;> simp
  rw [hm, Matrix.det_fin_two]
  norm_num

/-- A horizontal symmetry of a congruent image gives an actual reversing
symmetry of the original piece. -/
theorem conjugate_horizontal_symmetry {P Q : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' P = Q) (hQ : ReflectionSeparation.horizontal '' Q = Q) :
    ((e.trans ReflectionSeparation.horizontal).trans e.symm) '' P = P ∧
      (linearMatrix ((e.trans ReflectionSeparation.horizontal).trans e.symm)).det = -1 :=
  ⟨conjugate_image_eq e ReflectionSeparation.horizontal he hQ,
    (conjugate_det e ReflectionSeparation.horizontal).trans horizontal_det⟩

end Puzzling139335.N4Remainder
