import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicEquatorialPreimages
import Wikipedia.HomotopyGroupsOfSpheres.ComplexUnitaryCofactors

/-! # Cofactor norm constraints for unrestricted target preimages

These are consequences of the actual unitary matrix and its Schur pivot;
no determinant value or midpoint restriction is assumed.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices ComplexUnitaryEntryNorm

def pivotReferenceR (s t : ℝ) (B : Space (Fin 3)) : ℂ :=
  complexPart (referenceSquare s t) * star (pivotComplex s t B) +
    coordinate (referenceSquare s t) * star (pivotCoordinate s t B)

def pivotReferenceD (s t : ℝ) (B : Space (Fin 3)) : ℂ :=
  coordinate (referenceSquare s t) * pivotComplex s t B -
    complexPart (referenceSquare s t) * pivotCoordinate s t B

theorem target_pivot_minorOne (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    targetBeta * angleComplex s t * pivotReferenceD s t B =
      -(angleReal s t : ℂ) ^ 2 * B.val.val.det *
        star (B.val.val 2 1) * star (pivotCoordinate s t B) := by
  have he : minorOne (pivotImageR s t B) (pivotImageS s t B) =
      -(angleReal s t : ℂ) ^ 2 * B.val.val.det *
        star (B.val.val 1 2) * star (pivotCoordinate s t B) := by
    rw [← target_pivot_imageR s t B h, ← target_pivot_imageS s t B h, minorOne_smul]
    unfold pivotInputR pivotInputS
    rw [minorOne_mulVec_inputs]
    ring
  rw [symmetric_entry B 1 2] at he
  calc
    _ = minorOne (pivotImageR s t B) (pivotImageS s t B) := by
      simp [minorOne, pivotImageR, pivotImageS, pivotReferenceD, Matrix.cons_val_two]
      ring
    _ = _ := he

theorem target_pivot_referenceR_entry (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    (angleReal s t : ℂ) * star (pivotCoordinate s t B) * B.val.val 2 1 =
      targetBeta * pivotReferenceR s t B := by
  have h0 := target_pivot_complex_two s t B h
  have h1 := target_pivot_coordinate_two s t B h
  unfold pivotReferenceR
  simp only [Complex.star_def] at h0 h1 ⊢
  linear_combination (starRingEnd ℂ) (pivotCoordinate s t B) * h1 +
    (starRingEnd ℂ) (pivotComplex s t B) * h0

theorem cofactor_norm_balance (β w D r δ v q : ℂ) (c : ℝ)
    (hβ : β ≠ 0) (hδ : Complex.normSq δ = 1)
    (he : β * w * D = -(c : ℂ) ^ 2 * δ * star v * star q)
    (hr : (c : ℂ) * star q * v = β * r) :
    Complex.normSq w * Complex.normSq D = c ^ 2 * Complex.normSq r := by
  have h1 := congrArg Complex.normSq he
  have h2 := congrArg Complex.normSq hr
  simp only [map_mul, Complex.normSq_neg, map_pow, Complex.normSq_ofReal,
    Complex.star_def, Complex.normSq_conj, hδ, mul_one] at h1 h2
  apply mul_left_cancel₀ (ne_of_gt (Complex.normSq_pos.mpr hβ))
  linear_combination h1 + c ^ 2 * h2

theorem target_pivot_reference_norm_balance (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    Complex.normSq (angleComplex s t) * Complex.normSq (pivotReferenceD s t B) =
      angleReal s t ^ 2 * Complex.normSq (pivotReferenceR s t B) := by
  exact cofactor_norm_balance targetBeta _ _ _ B.val.val.det (B.val.val 2 1)
    (pivotCoordinate s t B) (angleReal s t) targetBeta_ne_zero (normSq_det B.val)
    (target_pivot_minorOne s t B h) (target_pivot_referenceR_entry s t B h)

theorem complex_reference_pair_norm (H L p q : ℂ) (hL : star L = L)
    (hu : H * star H + L ^ 2 = 1) :
    Complex.normSq (H * star p + L * star q) + Complex.normSq (L * p - H * q) =
      Complex.normSq p + Complex.normSq q := by
  have hn (z : ℂ) : (Complex.normSq z : ℂ) = star z * z :=
    Complex.normSq_eq_conj_mul_self
  have hc : ((Complex.normSq (H * star p + L * star q) +
      Complex.normSq (L * p - H * q) : ℝ) : ℂ) =
      ((Complex.normSq p + Complex.normSq q : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, hn, star_add, star_sub, star_mul, star_star, hL]
    linear_combination (star p * p + star q * q) * hu
  exact_mod_cast hc

theorem pivot_reference_pair_norm (s t : ℝ) (B : Space (Fin 3)) :
    Complex.normSq (pivotReferenceR s t B) + Complex.normSq (pivotReferenceD s t B) =
      Quaternion.normSq (schurPivot s t B) := by
  rw [normSq_complex_pair]
  exact complex_reference_pair_norm _ _ _ _ (referenceSquare_coordinate_star s t)
    (referenceSquare_complex_unit s t)

theorem target_pivot_referenceR_norm (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    Complex.normSq (pivotReferenceR s t B) =
      Complex.normSq (angleComplex s t) * Quaternion.normSq (schurPivot s t B) := by
  have he := target_pivot_reference_norm_balance s t B h
  have hp := pivot_reference_pair_norm s t B
  have hu := angle_norm s t
  linear_combination -he + Complex.normSq (angleComplex s t) * hp -
    Complex.normSq (pivotReferenceR s t B) * hu

theorem target_pivot_norm_constraint (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn) :
    4 * Complex.normSq (pivotComplex s t B +
      (1 + ((Quaternion.normSq (schurPivot s t B) : ℝ) : ℂ)) * angleComplex s t) =
      Complex.normSq (angleComplex s t) * Quaternion.normSq (schurPivot s t B) := by
  have he := congrArg Complex.normSq (target_pivot_symmetry s t B h)
  have hα : Complex.normSq targetAlpha = 1 / 4 := by norm_num [targetAlpha]
  change Complex.normSq (_ + _) = Complex.normSq (targetAlpha * pivotReferenceR s t B) at he
  rw [map_mul, hα, target_pivot_referenceR_norm s t B h] at he
  rw [add_comm, mul_comm (1 + _)]
  linarith

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
