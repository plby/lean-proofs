import Wikipedia.HopfProblem.ConifoldPolarTargetAlgebraPositive
import Wikipedia.HopfProblem.ConifoldPolarTargetAlgebraUnitary
import Wikipedia.HopfProblem.ConifoldPolarMatrixAlgebra

/-!
# Recovery of the explicit polar target factors

Multiplying the displayed positive and unitary matrices gives a
determinant-one matrix.  The original polar formulas recover those same
factors and the original Euclidean coordinates, without a transported map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

theorem det_inverseMatrix (b : Base) (z : Normal) (hz : ‖z‖ = 1) :
    (inverseMatrix b z).det = 1 := by
  rw [inverseMatrix, Matrix.det_mul, det_positiveMatrix, one_mul,
    det_unitaryMatrix, hz, one_pow, Complex.ofReal_one]

theorem frobeniusSq_inverseMatrix (b : Base) (z : Normal) (hz : ‖z‖ = 1) :
    frobeniusSq (inverseMatrix b z) = 2 + 4 * ‖b‖ ^ 2 := by
  rw [inverseMatrix, frobeniusSq_mul_of_mul_conjTranspose _ _
    (unitaryMatrix_mul_conjTranspose z hz), frobeniusSq_positiveMatrix]

theorem denominator_inverseMatrix (b : Base) (z : Normal) (hz : ‖z‖ = 1) :
    denominator (inverseMatrix b z) = 2 * hyperbolicScale b := by
  have hd := denominator_sq (inverseMatrix b z)
  rw [frobeniusSq_inverseMatrix b z hz] at hd
  nlinarith [denominator_pos (inverseMatrix b z),
    hyperbolicScale_sq b, hyperbolicScale_pos b]

theorem deform_one_inverseMatrix (b : Base) (z : Normal) :
    deform 1 (inverseMatrix b z) =
      (2 * hyperbolicScale b : ℂ) • unitaryMatrix z := by
  rw [inverseMatrix, deform, adjointAdjugate_mul,
    adjointAdjugate_unitaryMatrix, Complex.ofReal_one, one_smul,
    ← Matrix.add_mul, positiveMatrix_add_adjointAdjugate, Matrix.smul_mul, one_mul]

theorem unitaryPart_inverseMatrix (b : Base) (z : Normal) (hz : ‖z‖ = 1) :
    unitaryPart (inverseMatrix b z) = unitaryMatrix z := by
  rw [unitaryPart, denominator_inverseMatrix b z hz,
    deform_one_inverseMatrix, smul_smul]
  have hreal : (2 * hyperbolicScale b)⁻¹ * (2 * hyperbolicScale b) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero (by norm_num) (hyperbolicScale_ne_zero b))
  have hscalar : ((2 * hyperbolicScale b : ℝ) : ℂ)⁻¹ *
      (2 * hyperbolicScale b : ℂ) = 1 := by
    exact_mod_cast hreal
  rw [hscalar, one_smul]

theorem positivePart_inverseMatrix (b : Base) (z : Normal) (hz : ‖z‖ = 1) :
    positivePart (inverseMatrix b z) = positiveMatrix b := by
  rw [positivePart, unitaryPart_inverseMatrix b z hz, inverseMatrix,
    Matrix.mul_assoc, unitaryMatrix_mul_conjTranspose z hz, mul_one]

theorem baseCoordinates_positivePart_inverseMatrix
    (b : Base) (z : Normal) (hz : ‖z‖ = 1) :
    baseCoordinates (positivePart (inverseMatrix b z)) = b := by
  rw [positivePart_inverseMatrix b z hz, baseCoordinates_positiveMatrix]

theorem normalCoordinates_unitaryPart_inverseMatrix
    (b : Base) (z : Normal) (hz : ‖z‖ = 1) :
    normalCoordinates (unitaryPart (inverseMatrix b z)) = z := by
  rw [unitaryPart_inverseMatrix b z hz, normalCoordinates_unitaryMatrix]

end Wikipedia.HopfProblem.ConifoldPolar
