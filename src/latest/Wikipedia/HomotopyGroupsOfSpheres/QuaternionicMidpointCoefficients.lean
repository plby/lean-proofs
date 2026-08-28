import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductRotation
import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductSquaredCoordinates

/-!
# Nonvanishing coefficients for two midpoint preimage coordinates

After the real rotation, the first two squared coordinates are fixed by
the scalar phase. Both coefficient nonvanishing statements are proved.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

theorem traceRoot_eq : traceRoot = -rotationScale + Complex.I * (1 - rotationScale) := by
  apply Complex.ext <;> simp [traceRoot, rotationScale]

def midpointCoefficient (κ : ℂ) : ℂ :=
  -κ ^ 3 + star traceRoot * κ ^ 2 + traceRoot * κ - 1

theorem scaled_diagonalCoefficient (u : unitary ℂ) (hu : u.val ^ 3 = -1) (κ : ℂ) :
    diagonalCoefficient (u.val * κ) (-star u.val * traceRoot) = midpointCoefficient κ := by
  unfold diagonalCoefficient midpointCoefficient
  calc
    _ = u.val ^ 3 * (κ ^ 3 - star traceRoot * κ ^ 2) +
        (star u.val * u.val) * traceRoot * κ - 1 := by
      simp only [star_mul, star_neg, star_star]
      ring
    _ = _ := by rw [hu, u.property.1]; ring

def coefficientZeroMagnitude : ℝ :=
  (3 + 2 * (Real.sqrt 3 / 2) * (2 * (Real.sqrt 2 / 2) - 1)) / 2

theorem coefficientZeroMagnitude_pos : 0 < coefficientZeroMagnitude := by
  have htwo : 1 < Real.sqrt (2 : ℝ) := by
    exact (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)
  have hthree : 0 < Real.sqrt (3 : ℝ) / 2 := by positivity
  unfold coefficientZeroMagnitude
  have hp : 0 < 2 * (Real.sqrt 3 / 2) * (2 * (Real.sqrt 2 / 2) - 1) := by
    apply mul_pos
    · positivity
    · linarith
  linarith

theorem midpointCoefficient_zero :
    midpointCoefficient (targetEigenvalues 0) =
      -(1 + Complex.I) * (coefficientZeroMagnitude : ℂ) := by
  have hc : (coefficientZeroMagnitude : ℂ) =
      (3 + 2 * targetBeta * (2 * rotationScale - 1)) / 2 := by
    simp [coefficientZeroMagnitude, targetBeta, rotationScale]
  have hb3 : targetBeta ^ 3 = (3 / 4 : ℂ) * targetBeta := by
    rw [pow_succ, targetBeta_sq]
  rw [hc]
  simp only [midpointCoefficient, targetEigenvalues, Matrix.cons_val_zero,
    targetAlpha, traceRoot_eq, star_add, star_neg, star_mul, star_sub,
    star_one, rotationScale_star, Complex.star_def, Complex.conj_I]
  ring_nf
  norm_num [targetBeta_sq, hb3, Complex.I_sq, Complex.I_pow_three]
  ring_nf

theorem midpointCoefficient_one :
    midpointCoefficient (targetEigenvalues 1) = -((2 + Real.sqrt 2 : ℝ) : ℂ) := by
  simp [midpointCoefficient, targetEigenvalues, traceRoot_eq, rotationScale]
  ring

theorem midpointCoefficient_zero_ne_zero : midpointCoefficient (targetEigenvalues 0) ≠ 0 := by
  rw [midpointCoefficient_zero]
  apply mul_ne_zero
  · apply neg_ne_zero.mpr
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt coefficientZeroMagnitude_pos)

theorem midpointCoefficient_one_ne_zero : midpointCoefficient (targetEigenvalues 1) ≠ 0 := by
  rw [midpointCoefficient_one]
  apply neg_ne_zero.mpr
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity : 0 < (2 : ℝ) + Real.sqrt 2))

theorem midpointCoefficient_first_two_ne_zero (r : Fin 2) :
    midpointCoefficient (targetEigenvalues r.castSucc) ≠ 0 := by
  fin_cases r
  · exact midpointCoefficient_zero_ne_zero
  · exact midpointCoefficient_one_ne_zero

theorem midpoint_same_first_two_squares (z w : UnitSphere) (u : unitary ℂ)
    (hu : u.val ^ 3 = -1)
    (hz : (symmetricMap z).val.val = u.val • targetMatrix targetAlpha targetBeta)
    (hw : (symmetricMap w).val.val = u.val • targetMatrix targetAlpha targetBeta) (r : Fin 2) :
    (rotationSphere z).val r.castSucc ^ 2 = (rotationSphere w).val r.castSucc ^ 2 := by
  apply diagonal_same_squared_coordinate (rotationSphere z) (rotationSphere w)
    (fun q ↦ u.val * targetEigenvalues q) (midpoint_diagonalized z u.val hz)
    (midpoint_diagonalized w u.val hw)
  · rw [midpoint_rotated_squareSum z u hu hz, midpoint_rotated_squareSum w u hu hw]
  · rw [midpoint_rotated_squareSum z u hu hz, scaled_diagonalCoefficient u hu]
    exact midpointCoefficient_first_two_ne_zero r

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
