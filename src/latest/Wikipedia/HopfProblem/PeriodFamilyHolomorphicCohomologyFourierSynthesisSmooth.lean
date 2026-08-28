import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisRegularity

/-!
# The actual smooth Fourier synthesis over the original open base

The original rapidly decreasing parameter coefficients define their
literal infinite Fourier series. Compact-uniform summable operator bounds
justify its termwise real differentiation, and finite-dimensional
induction proves joint real smoothness to every order. The resulting
`FourierSynthesis.smoothFamily` is an actual function on the original open
base times the original unit torus, with the usual quotient lift.

This package proves analytic synthesis, not relative cohomological local
generation, local freeness, or specialized higher-direct-image base change.
-/
