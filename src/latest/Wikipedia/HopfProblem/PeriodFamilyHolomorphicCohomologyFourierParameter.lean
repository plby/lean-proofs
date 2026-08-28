import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDecay

/-!
# Actual compact-parameter Fourier estimates

The coefficients are the original normalized Haar Fourier coefficients on
the fixed unit torus. Joint continuity gives continuous coefficients and
continuous fibre sup norms, without extra topological assumptions on the
parameter space.

For a genuinely jointly smooth family over an open complex base, vertical
differentiation preserves joint smoothness and agrees exactly with the
existing fibrewise torus operator. Iterating the actual coordinate elliptic
operators then supplies one rapid-decay constant on each compact parameter
set. The constant comes from the sup norms of this actual differential
operator, not from an assumed Fourier estimate.

The raw endpoints require only real smoothness of the original quotient
lift on the open base. No boundary regularity, coefficient-decay hypothesis,
infinite-series reconstruction, or cohomological base-change claim is used.
-/
