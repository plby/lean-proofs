import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothForward
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothModes

/-!
# Real-smooth analytic inputs for the original varying period family

For an arbitrary original holomorphic period map on an open subset of the
complex line, this package proves joint real smoothness of its genuine
forward and inverse period-coordinate maps, its actual Dolbeault symbol,
and each scalar and top-degree Hermitian Fourier multiplier. The native
statements use the original complex charts with scalars restricted to the
reals. No period-dependent replacement atlas or regularity premise is used.

The ambient coordinate formulas agree with the native maps throughout the
original open base. Their smoothness is asserted only on that open domain,
not across its boundary. This supplies finite-mode analytic input; it does
not assert convergence of a parameter-dependent infinite Fourier series,
cohomology comparison, or base change.
-/
