import Wikipedia.HopfProblem.ConifoldPolarMatrixAlgebraPositive

/-!
# Raw matrix identities for the explicit two-by-two polar formula

For a literal complex matrix of determinant one, the normalized adjugate
formula gives a determinant-one unitary matrix.  The remaining factor is
Hermitian, has determinant one and positive trace, and reconstructs the input
by ordinary matrix multiplication.  No polar decomposition is assumed.
-/

open scoped ComplexConjugate ComplexOrder

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

theorem frobeniusSq_nonneg (M : MatrixSpace) : 0 ≤ frobeniusSq M := by
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (M i j)

theorem denominator_pos (M : MatrixSpace) : 0 < denominator M := by
  apply Real.sqrt_pos.mpr
  linarith [frobeniusSq_nonneg M]

theorem denominator_ne_zero (M : MatrixSpace) : denominator M ≠ 0 :=
  ne_of_gt (denominator_pos M)

theorem denominator_sq (M : MatrixSpace) :
    denominator M ^ 2 = frobeniusSq M + 2 := by
  apply Real.sq_sqrt
  linarith [frobeniusSq_nonneg M]

theorem adjointAdjugate_mul (M N : MatrixSpace) :
    adjointAdjugate (M * N) = adjointAdjugate M * adjointAdjugate N := by
  simp only [adjointAdjugate, Matrix.conjTranspose_mul, Matrix.adjugate_mul_distrib]

theorem adjointAdjugate_unitaryPart (M : MatrixSpace) :
    adjointAdjugate (unitaryPart M) = unitaryPart M := by
  unfold unitaryPart
  simp only [← Complex.ofReal_inv]
  rw [adjointAdjugate_smul, adjointAdjugate_deform]
  simp only [deform, Complex.ofReal_one, one_smul, add_comm]

theorem conjTranspose_adjointAdjugate (M : MatrixSpace) :
    (adjointAdjugate M).conjTranspose = M.adjugate := by
  simp only [adjointAdjugate, Matrix.adjugate_conjTranspose,
    Matrix.conjTranspose_conjTranspose]

theorem adjugate_unitaryPart (M : MatrixSpace) :
    (unitaryPart M).adjugate = (unitaryPart M).conjTranspose := by
  have h := congrArg Matrix.conjTranspose (adjointAdjugate_unitaryPart M)
  simpa only [conjTranspose_adjointAdjugate] using h

theorem det_unitaryPart (M : MatrixSpace) (hM : M.det = 1) :
    (unitaryPart M).det = 1 := by
  have hd : (denominator M : ℂ) ≠ 0 := by
    exact_mod_cast denominator_ne_zero M
  have hsq : (denominator M : ℂ) ^ 2 = (frobeniusSq M : ℂ) + 2 := by
    exact_mod_cast denominator_sq M
  rw [unitaryPart, Matrix.det_smul, Fintype.card_fin, det_deform, hM]
  simp only [Complex.ofReal_one, one_pow, one_mul, map_one]
  calc
    (denominator M : ℂ)⁻¹ ^ 2 * (1 + (frobeniusSq M : ℂ) + 1) =
        (denominator M : ℂ)⁻¹ ^ 2 * (denominator M : ℂ) ^ 2 := by
      rw [hsq]
      ring
    _ = 1 := by field_simp

theorem unitaryPart_mul_conjTranspose (M : MatrixSpace) (hM : M.det = 1) :
    unitaryPart M * (unitaryPart M).conjTranspose = 1 := by
  rw [← adjugate_unitaryPart, Matrix.mul_adjugate, det_unitaryPart M hM, one_smul]

theorem conjTranspose_mul_unitaryPart (M : MatrixSpace) (hM : M.det = 1) :
    (unitaryPart M).conjTranspose * unitaryPart M = 1 := by
  rw [← adjugate_unitaryPart, Matrix.adjugate_mul, det_unitaryPart M hM, one_smul]

/-- The Hermitian factor is a positive scalar times `M M* + I`. -/
theorem positivePart_formula (M : MatrixSpace) (hM : M.det = 1) :
    positivePart M =
      ((denominator M)⁻¹ : ℂ) • (M * M.conjTranspose + (1 : MatrixSpace)) := by
  simp only [positivePart, unitaryPart, Matrix.conjTranspose_smul,
    Complex.star_def, map_inv₀, Complex.conj_ofReal, Matrix.mul_smul, deform,
    Complex.ofReal_one, one_smul, Matrix.conjTranspose_add,
    conjTranspose_adjointAdjugate, Matrix.mul_add, Matrix.mul_adjugate, hM]

theorem positivePart_isHermitian (M : MatrixSpace) (hM : M.det = 1) :
    (positivePart M).IsHermitian := by
  rw [Matrix.IsHermitian, positivePart_formula M hM]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_one, Complex.star_def, map_inv₀, Complex.conj_ofReal]

/-- Positive definiteness is proved from the literal normalized `M M* + I` formula. -/
theorem positivePart_posDef (M : MatrixSpace) (hM : M.det = 1) :
    (positivePart M).PosDef := by
  rw [positivePart_formula M hM, ← Complex.ofReal_inv]
  exact posDef_smul_self_mul_conjTranspose_add_one M (inv_pos.mpr (denominator_pos M))

theorem det_positivePart (M : MatrixSpace) (hM : M.det = 1) :
    (positivePart M).det = 1 := by
  simp only [positivePart, Matrix.det_mul, Matrix.det_conjTranspose,
    hM, det_unitaryPart M hM, star_one, mul_one]

theorem trace_mul_conjTranspose (M : MatrixSpace) :
    (M * M.conjTranspose).trace = (frobeniusSq M : ℂ) := by
  simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    frobeniusSq_entries, Complex.ofReal_add, Complex.mul_conj]

theorem frobeniusSq_mul_of_mul_conjTranspose (M U : MatrixSpace)
    (hU : U * U.conjTranspose = 1) : frobeniusSq (M * U) = frobeniusSq M := by
  have hm : (M * U) * (M * U).conjTranspose = M * M.conjTranspose := by
    rw [Matrix.conjTranspose_mul]
    calc
      (M * U) * (U.conjTranspose * M.conjTranspose) =
          (M * (U * U.conjTranspose)) * M.conjTranspose := by
        simp only [Matrix.mul_assoc]
      _ = M * M.conjTranspose := by rw [hU, mul_one]
  apply Complex.ofReal_injective
  simpa only [trace_mul_conjTranspose] using congrArg Matrix.trace hm

theorem trace_positivePart (M : MatrixSpace) (hM : M.det = 1) :
    (positivePart M).trace = (denominator M : ℂ) := by
  rw [positivePart_formula M hM, Matrix.trace_smul, Matrix.trace_add,
    trace_mul_conjTranspose, Matrix.trace_one]
  simp only [Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul]
  have h : (denominator M)⁻¹ * (frobeniusSq M + 2) = denominator M := by
    rw [← denominator_sq M]
    field_simp [denominator_ne_zero M]
  simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_add,
    Complex.ofReal_ofNat] using congrArg (fun x : ℝ => (x : ℂ)) h

theorem trace_positivePart_re_pos (M : MatrixSpace) (hM : M.det = 1) :
    0 < (positivePart M).trace.re := by
  rw [trace_positivePart M hM, Complex.ofReal_re]
  exact denominator_pos M

theorem positivePart_mul_unitaryPart (M : MatrixSpace) (hM : M.det = 1) :
    positivePart M * unitaryPart M = M := by
  rw [positivePart, Matrix.mul_assoc, conjTranspose_mul_unitaryPart M hM, mul_one]

end Wikipedia.HopfProblem.ConifoldPolar
