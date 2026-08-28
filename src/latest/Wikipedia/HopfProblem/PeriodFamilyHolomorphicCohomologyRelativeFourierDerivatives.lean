import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFourierDerivativesNaturality

/-!
# Uniform all-order base derivatives of the actual inverse Fourier modes

For every original holomorphic period family on an open subset of the
complex plane and every base point, one fixed inner disc works for all
integer Fourier modes and all complex derivative orders. The actual
inverse-mode derivative of order `n` is bounded there by
`n! * c⁻¹ / r^n * ‖k‖⁻¹`, with `r,c > 0` proved to exist. The surrounding
outer closed disc lies in the original base.

Ambient representatives agree literally with the original inverse modes,
are genuinely holomorphic on the needed open neighborhood, and their
derivatives are independent of all choices outside the original base.
Every derivative of the zero mode is zero. No infinite Fourier sum or
higher-direct-image theorem is asserted by this package.
-/
