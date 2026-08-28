import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointPhases
import Wikipedia.HomotopyGroupsOfSpheres.ComplexTraceEquation

/-!
# The squared-coordinate sum of a midpoint sphere preimage

For each allowed scalar phase the trace equation fixes the sum of the
squared complex coordinates. This is a necessary preimage constraint.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open ComplexCrossProductUnitary

theorem targetMatrix_trace : (targetMatrix targetAlpha targetBeta).trace = 1 + Complex.I := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_three, targetMatrix, targetAlpha,
    Matrix.cons_val_two]
  ring

theorem unitary_cube_square (u : unitary ℂ) (hu : u.val ^ 3 = -1) :
    u.val ^ 2 = -star u.val := by
  calc
    u.val ^ 2 = u.val ^ 2 * (u.val * star u.val) := by rw [u.property.2, mul_one]
    _ = u.val ^ 3 * star u.val := by ring
    _ = -star u.val := by rw [hu]; ring

theorem unitary_complex_norm (u : unitary ℂ) : ‖u.val‖ = 1 := by
  have hn := congrArg norm u.property.2
  rw [norm_mul, norm_star, norm_one] at hn
  nlinarith [norm_nonneg u.val]

theorem midpoint_squareSum (z : UnitSphere) (u : unitary ℂ) (hu : u.val ^ 3 = -1)
    (hB : (symmetricMap z).val.val = u.val • targetMatrix targetAlpha targetBeta) :
    squareSum z.val = -star u.val * traceRoot := by
  have ht : squareSum z.val ^ 2 + 2 * star (squareSum z.val) = u.val * (1 + Complex.I) := by
    rw [← symmetricMap_trace, hB, Matrix.trace_smul, targetMatrix_trace]
    rfl
  have hn : ‖-u.val * squareSum z.val‖ ≤ 1 := by
    rw [norm_mul, norm_neg, unitary_complex_norm, one_mul]
    exact norm_squareSum_le_one z
  have he : (-u.val * squareSum z.val) ^ 2 + 2 * star (-u.val * squareSum z.val) =
      -1 - Complex.I := by
    calc
      _ = u.val ^ 2 * squareSum z.val ^ 2 - 2 * star u.val * star (squareSum z.val) := by
        simp only [star_mul, star_neg]
        ring
      _ = -star u.val * (squareSum z.val ^ 2 + 2 * star (squareSum z.val)) := by
        rw [unitary_cube_square u hu]
        ring
      _ = -(star u.val * u.val) * (1 + Complex.I) := by rw [ht]; ring
      _ = -1 - Complex.I := by rw [u.property.1]; ring
  have hroot := trace_equation_unique _ hn he
  calc
    squareSum z.val = (star u.val * u.val) * squareSum z.val := by rw [u.property.1, one_mul]
    _ = -star u.val * (-u.val * squareSum z.val) := by ring
    _ = -star u.val * traceRoot := by rw [hroot]

theorem midpoint_preimage_squareSum (z : UnitSphere)
    (h : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    ∃ u : unitary ℂ, u.val ^ 3 = -1 ∧
      (symmetricMap z).val.val = u.val • targetMatrix targetAlpha targetBeta ∧
      squareSum z.val = -star u.val * traceRoot := by
  obtain ⟨u, hu, hB⟩ := midpoint_target_forward (symmetricMap z) (symmetricMap_det z) h
  exact ⟨u, hu, hB, midpoint_squareSum z u hu hB⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
