import Wikipedia.HopfProblem.ConifoldPolarNativeFramingDefs

/-!
# Native conifold image lines and their Gram matrices

The Gram matrix of the original small-resolution map is computed in its
unchanged finite chart and at infinity.  On the unit normal radius its
traceless Hermitian coordinates are exactly half the explicitly marked
image-line direction.
-/

open OnePoint
open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open ConifoldStandardBoundary CuspCircleNormalTrivialization

theorem baseCoordinates_add (M N : MatrixSpace) :
    baseCoordinates (M + N) = baseCoordinates M + baseCoordinates N := by
  ext i
  fin_cases i <;> simp [baseCoordinates]
  ring

theorem baseCoordinates_real_smul (a : ℝ) (M : MatrixSpace) :
    baseCoordinates ((a : ℂ) • M) = a • baseCoordinates M := by
  ext i
  fin_cases i <;> simp [baseCoordinates]
  ring

theorem baseCoordinates_one : baseCoordinates (1 : MatrixSpace) = 0 := by
  ext i
  fin_cases i <;> simp [baseCoordinates]

theorem lowerMatrix_gram (a : ℂ) (F : Fibre) :
    Conifold.lowerMatrix a F * (Conifold.lowerMatrix a F).conjTranspose =
      ((Complex.normSq F.1 + Complex.normSq F.2 : ℝ) : ℂ) •
        !![1, conj a; a, (Complex.normSq a : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Conifold.lowerMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self] <;> ring

theorem upperMatrix_zero_gram (F : Fibre) :
    Conifold.upperMatrix 0 F * (Conifold.upperMatrix 0 F).conjTranspose =
      ((Complex.normSq F.1 + Complex.normSq F.2 : ℝ) : ℂ) •
        !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Conifold.upperMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_two, Complex.ofReal_add, Complex.normSq_eq_conj_mul_self]
  ring

theorem lowerInverse_row_norm (a : ℂ) (F : Fibre) (hF : radiusSq F = 1) :
    Complex.normSq (lowerInverse a F).1 + Complex.normSq (lowerInverse a F).2 =
      (Complex.normSq a + 1)⁻¹ := by
  have h := Conifold.frobeniusSq_lowerMatrix_lowerInverse a F
  rw [Conifold.frobeniusSq_lowerMatrix] at h
  change CuspCircleNormalTrivialization.denominator a *
      (Complex.normSq (lowerInverse a F).1 + Complex.normSq (lowerInverse a F).2) =
        radiusSq F at h
  rw [hF] at h
  have hinv : Complex.normSq (lowerInverse a F).1 + Complex.normSq (lowerInverse a F).2 =
      (CuspCircleNormalTrivialization.denominator a)⁻¹ := by
    calc
      _ = (CuspCircleNormalTrivialization.denominator a)⁻¹ *
          (CuspCircleNormalTrivialization.denominator a *
            (Complex.normSq (lowerInverse a F).1 +
              Complex.normSq (lowerInverse a F).2)) := by
        rw [← mul_assoc,
          inv_mul_cancel₀ (CuspCircleNormalTrivialization.denominator_ne_zero a), one_mul]
      _ = _ := by rw [h, mul_one]
  simpa only [CuspCircleNormalTrivialization.denominator, add_comm] using hinv

theorem productMap_gram_coe (a : ℂ) (F : Fibre) (hF : radiusSq F = 1) :
    Conifold.productMap ((a : RiemannSphere), F) *
        (Conifold.productMap ((a : RiemannSphere), F)).conjTranspose =
      (((Complex.normSq a + 1)⁻¹ : ℝ) : ℂ) •
        !![1, conj a; a, (Complex.normSq a : ℂ)] := by
  change Conifold.lowerMatrix a (lowerInverse a F) *
      (Conifold.lowerMatrix a (lowerInverse a F)).conjTranspose = _
  rw [lowerMatrix_gram, lowerInverse_row_norm a F hF]

theorem productMap_gram_infty (F : Fibre) (hF : radiusSq F = 1) :
    Conifold.productMap ((∞ : RiemannSphere), F) *
        (Conifold.productMap ((∞ : RiemannSphere), F)).conjTranspose =
      !![0, 0; 0, 1] := by
  have h := Conifold.frobeniusSq_upperMatrix_upperInverse 0 F
  rw [Conifold.frobeniusSq_upperMatrix] at h
  change CuspCircleNormalTrivialization.denominator 0 *
      (Complex.normSq (upperInverse 0 F).1 + Complex.normSq (upperInverse 0 F).2) =
        radiusSq F at h
  simp only [CuspCircleNormalTrivialization.denominator, Complex.normSq_zero,
    add_zero, one_mul, hF] at h
  change Conifold.upperMatrix 0 (upperInverse 0 F) *
      (Conifold.upperMatrix 0 (upperInverse 0 F)).conjTranspose = _
  rw [upperMatrix_zero_gram, h, Complex.ofReal_one, one_smul]

/-- The original image-line direction, with the prescribed Hermitian coordinate signs. -/
theorem baseCoordinates_productMap_gram (p : RiemannSphere × Fibre)
    (hp : radiusSq p.2 = 1) :
    baseCoordinates (Conifold.productMap p * (Conifold.productMap p).conjTranspose) =
      (1 / 2 : ℝ) • lineDirection p.1 := by
  rcases p with ⟨p, F⟩
  induction p using OnePoint.rec with
  | infty =>
      rw [productMap_gram_infty F hp]
      ext i
      fin_cases i <;> norm_num [baseCoordinates, lineDirection]
  | coe a =>
      rw [productMap_gram_coe a F hp, baseCoordinates_real_smul]
      ext i
      fin_cases i <;> simp [baseCoordinates, lineDirection, div_eq_mul_inv] <;> ring

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
