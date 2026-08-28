import Wikipedia.HopfProblem.ConifoldPolarDefs

/-!
# The explicit positive factor in standard polar coordinates

The three given Euclidean coordinates determine a literal Hermitian
determinant-one matrix.  All identities use its displayed two-by-two entries.
-/

noncomputable section

open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

theorem base_norm_sq (b : Base) :
    ‖b‖ ^ 2 = (b 0) ^ 2 + (b 1) ^ 2 + (b 2) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  ring

theorem hyperbolicScale_pos (b : Base) : 0 < hyperbolicScale b := by
  apply Real.sqrt_pos.mpr
  positivity

theorem hyperbolicScale_ne_zero (b : Base) : hyperbolicScale b ≠ 0 :=
  ne_of_gt (hyperbolicScale_pos b)

theorem hyperbolicScale_sq (b : Base) : hyperbolicScale b ^ 2 = 1 + ‖b‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

theorem norm_lt_hyperbolicScale (b : Base) : ‖b‖ < hyperbolicScale b := by
  nlinarith [hyperbolicScale_sq b, hyperbolicScale_pos b, norm_nonneg b]

theorem positiveMatrix_entries (b : Base) :
    positiveMatrix b =
      !![(hyperbolicScale b : ℂ) + (b 0 : ℂ), (b 1 : ℂ) + (b 2 : ℂ) * Complex.I;
        (b 1 : ℂ) - (b 2 : ℂ) * Complex.I, (hyperbolicScale b : ℂ) - (b 0 : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [positiveMatrix, tracelessMatrix, sub_eq_add_neg]

theorem positiveMatrix_conjTranspose (b : Base) :
    (positiveMatrix b).conjTranspose = positiveMatrix b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positiveMatrix_entries, Matrix.conjTranspose_apply, sub_eq_add_neg]

theorem det_positiveMatrix (b : Base) : (positiveMatrix b).det = 1 := by
  have hs := hyperbolicScale_sq b
  rw [base_norm_sq] at hs
  apply Complex.ext <;>
    simp [positiveMatrix_entries, Matrix.det_fin_two] <;> nlinarith [hs]

theorem baseCoordinates_positiveMatrix (b : Base) :
    baseCoordinates (positiveMatrix b) = b := by
  ext i
  fin_cases i <;> simp [baseCoordinates, positiveMatrix_entries]

theorem trace_positiveMatrix (b : Base) :
    (positiveMatrix b).trace = (2 * hyperbolicScale b : ℝ) := by
  simp [Matrix.trace, Fin.sum_univ_two, positiveMatrix_entries]
  ring

theorem trace_positiveMatrix_re_pos (b : Base) :
    0 < (positiveMatrix b).trace.re := by
  rw [trace_positiveMatrix]
  simpa only [Complex.ofReal_re] using mul_pos (by norm_num : (0 : ℝ) < 2)
    (hyperbolicScale_pos b)

theorem adjointAdjugate_positiveMatrix_add (b : Base) :
    adjointAdjugate (positiveMatrix b) + positiveMatrix b =
      (2 * hyperbolicScale b : ℂ) • (1 : MatrixSpace) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adjointAdjugate_entries, positiveMatrix_entries] <;> ring

theorem positiveMatrix_add_adjointAdjugate (b : Base) :
    positiveMatrix b + adjointAdjugate (positiveMatrix b) =
      (2 * hyperbolicScale b : ℂ) • (1 : MatrixSpace) := by
  rw [add_comm, adjointAdjugate_positiveMatrix_add]

theorem frobeniusSq_positiveMatrix (b : Base) :
    frobeniusSq (positiveMatrix b) = 2 + 4 * ‖b‖ ^ 2 := by
  have hs := hyperbolicScale_sq b
  rw [base_norm_sq] at hs ⊢
  simp [frobeniusSq_entries, positiveMatrix_entries, Complex.normSq_apply]
  nlinarith [hs]

end Wikipedia.HopfProblem.ConifoldPolar
