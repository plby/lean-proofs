import Wikipedia.HopfProblem.PeriodTorusTypeOneOneKernelBasis

/-!
# The exact period polynomial as an actual tangent-form obstruction

This is the six-coefficient polynomial of Lemma 9.2. Its real and imaginary
parts are computed as evaluations of the genuine transported form in a
proved complex basis. No cohomology or Hodge decomposition is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open Complex

/-- The period polynomial for an actual integral alternating coefficient form. -/
def periodPolynomial (p : PeriodPoint) (E : Fin 6 → ℤ) : ℂ :=
  (E 0 : ℂ) - (E 1 : ℂ) * p.τ - (E 2 : ℂ) * p.μ +
    6 * (E 3 : ℂ) * p.μ + (E 4 : ℂ) * p.β +
    (E 5 : ℂ) * (6 * p.μ ^ 2 - p.τ * p.β)

theorem periodPolynomial_re (p : PeriodPoint) (E : Fin 6 → ℤ) :
    (periodPolynomial p E).re =
      coordinateForm (fun k => (E k : ℝ)) (kernelRealFirst p) (kernelRealSecond p) -
        coordinateForm (fun k => (E k : ℝ)) (kernelImagFirst p) (kernelImagSecond p) := by
  simp [periodPolynomial, coordinateForm_apply, coordinateValue,
    kernelRealFirst, kernelRealSecond, kernelImagFirst, kernelImagSecond,
    Complex.mul_re, Complex.mul_im, pow_two]
  ring

theorem periodPolynomial_im (p : PeriodPoint) (E : Fin 6 → ℤ) :
    (periodPolynomial p E).im =
      coordinateForm (fun k => (E k : ℝ)) (kernelRealFirst p) (kernelImagSecond p) +
        coordinateForm (fun k => (E k : ℝ)) (kernelImagFirst p) (kernelRealSecond p) := by
  simp [periodPolynomial, coordinateForm_apply, coordinateValue,
    kernelRealFirst, kernelRealSecond, kernelImagFirst, kernelImagSecond,
    Complex.mul_re, Complex.mul_im, pow_two]
  ring

/-- The real obstruction is the failure of simultaneous `I`-invariance on the two basis vectors. -/
theorem periodPolynomial_re_tangent (p : PeriodDomain) (E : Fin 6 → ℤ) :
    (periodPolynomial p.val E).re =
      tangentForm p E (kernelBasisEquiv p e0) (kernelBasisEquiv p e1) -
        tangentForm p E (I • kernelBasisEquiv p e0) (I • kernelBasisEquiv p e1) := by
  rw [← periodEquiv_kernelImagFirst, ← periodEquiv_kernelImagSecond,
    ← periodEquiv_kernelRealFirst, ← periodEquiv_kernelRealSecond]
  simp only [tangentForm_periodEquiv]
  exact periodPolynomial_re p.val E

/-- The imaginary obstruction is the mixed complex-structure identity on the same basis. -/
theorem periodPolynomial_im_tangent (p : PeriodDomain) (E : Fin 6 → ℤ) :
    (periodPolynomial p.val E).im =
      tangentForm p E (kernelBasisEquiv p e0) (I • kernelBasisEquiv p e1) +
        tangentForm p E (I • kernelBasisEquiv p e0) (kernelBasisEquiv p e1) := by
  rw [← periodEquiv_kernelImagFirst, ← periodEquiv_kernelImagSecond,
    ← periodEquiv_kernelRealFirst, ← periodEquiv_kernelRealSecond]
  simp only [tangentForm_periodEquiv]
  exact periodPolynomial_im p.val E

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
