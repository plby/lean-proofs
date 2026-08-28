import Wikipedia.HopfProblem.PeriodTorusTypeOneOneEtaMatrix

/-!
# Pulling the Hermitian form back along the actual period columns

The period map here is the genuine real-linear period equivalence from
`PeriodTori.lean`.  The imaginary part of the Hermitian form pulls back to
`u ∧ w + 6 γ ∧ δ` in the column order `(γ̂, û, ŵ, δ̂)`.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

/-- The actual complex period columns applied to arbitrary real coefficients. -/
def etaPeriodVector (p : PeriodDomain) (r : Fin 4 → ℝ) : ComplexPlane₂ :=
  ![6 * p.val.μ * (r 0 : ℂ) + p.val.τ * (r 1 : ℂ) + (r 2 : ℂ),
    p.val.β * (r 0 : ℂ) + p.val.μ * (r 1 : ℂ) + (r 3 : ℂ)]

theorem etaPeriodVector_eq_matrix_mulVec (p : PeriodDomain) (r : Fin 4 → ℝ) :
    etaPeriodVector p r = p.val.matrix *ᵥ (fun i ↦ (r i : ℂ)) := by
  ext i
  fin_cases i <;>
    simp [etaPeriodVector, PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The displayed period formula is the existing period equivalence, not an
independent replacement for it. -/
theorem etaPeriodVector_eq_realEquiv (p : PeriodDomain) (r : Fin 4 → ℝ) :
    etaPeriodVector p r = (p.realEquiv.trans complexCoordinates) r := by
  rw [LinearEquiv.trans_apply, PeriodDomain.realEquiv_apply]
  ext i : 1
  fin_cases i <;> apply Complex.ext <;>
    simp [etaPeriodVector, complexCoordinates, PeriodPoint.realMatrix,
      dotProduct, Fin.sum_univ_four, Complex.mul_re, Complex.mul_im]

@[simp] theorem etaPeriodVector_add (p : PeriodDomain) (r s : Fin 4 → ℝ) :
    etaPeriodVector p (r + s) = etaPeriodVector p r + etaPeriodVector p s := by
  simp only [etaPeriodVector_eq_realEquiv, map_add]

@[simp] theorem etaPeriodVector_smul (p : PeriodDomain) (c : ℝ) (r : Fin 4 → ℝ) :
    etaPeriodVector p (c • r) = c • etaPeriodVector p r := by
  simp only [etaPeriodVector_eq_realEquiv, map_smul]

@[simp] theorem etaPeriodVector_zero_re (p : PeriodDomain) (r : Fin 4 → ℝ) :
    (etaPeriodVector p r 0).re = 6 * p.val.μ.re * r 0 + p.val.τ.re * r 1 + r 2 := by
  simp [etaPeriodVector, Complex.mul_re, Complex.mul_im]

@[simp] theorem etaPeriodVector_zero_im (p : PeriodDomain) (r : Fin 4 → ℝ) :
    (etaPeriodVector p r 0).im = 6 * p.val.μ.im * r 0 + p.val.τ.im * r 1 := by
  simp [etaPeriodVector, Complex.mul_re, Complex.mul_im]

@[simp] theorem etaPeriodVector_one_re (p : PeriodDomain) (r : Fin 4 → ℝ) :
    (etaPeriodVector p r 1).re = p.val.β.re * r 0 + p.val.μ.re * r 1 + r 3 := by
  simp [etaPeriodVector, Complex.mul_re]

@[simp] theorem etaPeriodVector_one_im (p : PeriodDomain) (r : Fin 4 → ℝ) :
    (etaPeriodVector p r 1).im = p.val.β.im * r 0 + p.val.μ.im * r 1 := by
  simp [etaPeriodVector, Complex.mul_im]

/-- The first row of the Hermitian matrix inverts the imaginary periods. -/
theorem etaHermitianMatrix_period_im_zero (p : PeriodDomain) (r : Fin 4 → ℝ) :
    etaHermitianMatrix p 0 0 * (etaPeriodVector p r 0).im +
      etaHermitianMatrix p 0 1 * (etaPeriodVector p r 1).im = r 1 := by
  rw [etaPeriodVector_zero_im, etaPeriodVector_one_im]
  simp only [etaHermitianMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [etaDenom_ne_zero p]
  unfold etaDenom
  ring

/-- The second row recovers six times the first integral-coordinate direction. -/
theorem etaHermitianMatrix_period_im_one (p : PeriodDomain) (r : Fin 4 → ℝ) :
    etaHermitianMatrix p 1 0 * (etaPeriodVector p r 0).im +
      etaHermitianMatrix p 1 1 * (etaPeriodVector p r 1).im = 6 * r 0 := by
  rw [etaPeriodVector_zero_im, etaPeriodVector_one_im]
  simp only [etaHermitianMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [etaDenom_ne_zero p]
  unfold etaDenom
  ring

/-- Grouping the imaginary part by the real matrix acting on imaginary coordinates. -/
theorem etaMatrixForm_im_eq (p : PeriodDomain) (x y : ComplexPlane₂) :
    (etaMatrixForm p x y).im =
      (etaHermitianMatrix p 0 0 * (x 0).im +
        etaHermitianMatrix p 0 1 * (x 1).im) * (y 0).re +
      (etaHermitianMatrix p 1 0 * (x 0).im +
        etaHermitianMatrix p 1 1 * (x 1).im) * (y 1).re -
      (x 0).re * (etaHermitianMatrix p 0 0 * (y 0).im +
        etaHermitianMatrix p 0 1 * (y 1).im) -
      (x 1).re * (etaHermitianMatrix p 1 0 * (y 0).im +
        etaHermitianMatrix p 1 1 * (y 1).im) := by
  simp only [etaMatrixForm, Fin.sum_univ_two, Complex.add_im, Complex.mul_im,
    Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, etaHermitianMatrix,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The imaginary part pulls back to exactly `u ∧ w + 6 γ ∧ δ` on all real
coefficient vectors, with no additional hypothesis on the period point. -/
theorem etaMatrixForm_im_periodVector (p : PeriodDomain) (r s : Fin 4 → ℝ) :
    (etaMatrixForm p (etaPeriodVector p r) (etaPeriodVector p s)).im =
      r 1 * s 2 - r 2 * s 1 + 6 * (r 0 * s 3 - r 3 * s 0) := by
  rw [etaMatrixForm_im_eq]
  simp only [etaHermitianMatrix_period_im_zero, etaHermitianMatrix_period_im_one,
    etaPeriodVector_zero_re, etaPeriodVector_one_re]
  ring

/-- The same pullback formula stated directly for the actual complex period matrix. -/
theorem etaMatrixForm_im_matrix_mulVec (p : PeriodDomain) (r s : Fin 4 → ℝ) :
    (etaMatrixForm p (p.val.matrix *ᵥ (fun i ↦ (r i : ℂ)))
      (p.val.matrix *ᵥ (fun i ↦ (s i : ℂ)))).im =
      r 1 * s 2 - r 2 * s 1 + 6 * (r 0 * s 3 - r 3 * s 0) := by
  rw [← etaPeriodVector_eq_matrix_mulVec, ← etaPeriodVector_eq_matrix_mulVec]
  exact etaMatrixForm_im_periodVector p r s

/-- The same pullback formula for the real-linear period equivalence used to
construct the actual complex tori. -/
theorem etaMatrixForm_im_realEquiv (p : PeriodDomain) (r s : Fin 4 → ℝ) :
    (etaMatrixForm p ((p.realEquiv.trans complexCoordinates) r)
      ((p.realEquiv.trans complexCoordinates) s)).im =
      r 1 * s 2 - r 2 * s 1 + 6 * (r 0 * s 3 - r 3 * s 0) := by
  rw [← etaPeriodVector_eq_realEquiv, ← etaPeriodVector_eq_realEquiv]
  exact etaMatrixForm_im_periodVector p r s

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
