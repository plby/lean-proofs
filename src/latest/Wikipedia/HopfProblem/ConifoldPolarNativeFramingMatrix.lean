import Wikipedia.HopfProblem.ConifoldPolarNativeFramingMatrixGram
import Wikipedia.HopfProblem.ConifoldPolarNativeFramingMatrixNormal

/-!
# The actual polar marking of the native unit normal boundary

The original normalized conifold matrix has positive factor
`(1/2) I + (3/2) M M*`, where `M` is the unchanged native conifold map.
Consequently its three real base coordinates are exactly `(3/4)` times the
marked image-line direction.  The imported normal-coordinate calculation
simultaneously identifies its four real normal coordinates with the original
normal coordinates, without any additional rotation or abstract equivalence.
-/

namespace Wikipedia.HopfProblem.ConifoldPolar.NativeFraming

open ConifoldStandardBoundary CuspCircleNormalTrivialization

theorem normalizedMatrix_linear_formula (p : RiemannSphere × Fibre) :
    normalizedMatrix p =
      ((1 / 2 : ℝ) : ℂ) • deform 1 (Conifold.productMap p) +
        ((3 / 2 : ℝ) : ℂ) • Conifold.productMap p := by
  have hA : adjointAdjugate ((2 : ℂ) • Conifold.productMap p) =
      (2 : ℂ) • adjointAdjugate (Conifold.productMap p) := by
    simpa only [Complex.ofReal_ofNat] using
      adjointAdjugate_smul (2 : ℝ) (Conifold.productMap p)
  rw [normalizedMatrix, ConifoldStandardBoundary.forward, deform, hA]
  ext i j
  norm_num [deform, coefficient, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The positive polar factor is computed from the original native image-line projection. -/
theorem positivePart_normalizedMatrix (p : RiemannSphere × Fibre)
    (hp : radiusSq p.2 = 1) :
    positivePart (normalizedMatrix p) =
      ((1 / 2 : ℝ) : ℂ) • (1 : MatrixSpace) +
        ((3 / 2 : ℝ) : ℂ) •
          (Conifold.productMap p * (Conifold.productMap p).conjTranspose) := by
  have hN := normalizedMatrix_linear_formula p
  rw [← unitaryPart_normalizedMatrix p hp] at hN
  have hU := unitaryPart_mul_conjTranspose (normalizedMatrix p) (det_normalizedMatrix p hp)
  have hMU : Conifold.productMap p * (unitaryPart (normalizedMatrix p)).conjTranspose =
      Conifold.productMap p * (Conifold.productMap p).conjTranspose := by
    rw [unitaryPart_normalizedMatrix p hp]
    simp only [deform, Complex.ofReal_one, one_smul, Matrix.conjTranspose_add,
      conjTranspose_adjointAdjugate, Matrix.mul_add, Matrix.mul_adjugate,
      Conifold.productMap_det, zero_smul, add_zero]
  calc
    positivePart (normalizedMatrix p) =
        (((1 / 2 : ℝ) : ℂ) • unitaryPart (normalizedMatrix p) +
          ((3 / 2 : ℝ) : ℂ) • Conifold.productMap p) *
            (unitaryPart (normalizedMatrix p)).conjTranspose :=
      congrArg (fun X : MatrixSpace => X * (unitaryPart (normalizedMatrix p)).conjTranspose) hN
    _ = _ := by
      rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hU, hMU]

/-- The exact native base marking on the unchanged unit normal boundary. -/
theorem baseCoordinates_positivePart_normalizedMatrix (p : RiemannSphere × Fibre)
    (hp : radiusSq p.2 = 1) :
    baseCoordinates (positivePart (normalizedMatrix p)) =
      (3 / 4 : ℝ) • lineDirection p.1 := by
  rw [positivePart_normalizedMatrix p hp, baseCoordinates_add,
    baseCoordinates_real_smul, baseCoordinates_real_smul,
    baseCoordinates_one, smul_zero, zero_add, baseCoordinates_productMap_gram p hp,
    smul_smul]
  norm_num

end Wikipedia.HopfProblem.ConifoldPolar.NativeFraming
