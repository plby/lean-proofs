import Wikipedia.HopfProblem.PeriodTorusTypeOneOnePolynomial
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneHermitianBasis

/-!
# Type `(1,1)` is exactly the source period-polynomial equation

This equivalence concerns genuine integral alternating forms transported
to the actual period-torus tangent model. It is proved by a complex basis
calculation, not by assuming a cohomological or Néron–Severi comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

/-- The genuine complex-structure condition is equivalent to the exact
six-coefficient polynomial in the actual periods. -/
theorem tangentForm_isTypeOneOne_iff (p : PeriodDomain) (E : Fin 6 → ℤ) :
    IsTypeOneOne (tangentForm p E) ↔ periodPolynomial p.val E = 0 := by
  rw [isTypeOneOne_iff_basis_equiv (tangentForm p E) (tangentForm_self p E)
    (kernelBasisEquiv p), Complex.ext_iff]
  simp only [Complex.zero_re, Complex.zero_im, periodPolynomial_re_tangent,
    periodPolynomial_im_tangent, sub_eq_zero]

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
