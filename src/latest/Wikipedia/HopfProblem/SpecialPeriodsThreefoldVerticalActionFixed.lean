import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedSphere
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedIndexing
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedCurveNormalWeights

/-!
# The actual fixed sphere and its normal weights

For the constructed effective fibrewise holomorphic `ℂˣ` action on the
original compact threefold, the native group-action fixed set is exactly
`D₀ = CuspGeometry.doubleCurve 1`. The original two cusp-axis charts give
an actual biholomorphism from the Riemann sphere to this literal subspace,
and its ambient parametrization is a closed holomorphic immersion. The
two original triple points are its marked endpoints.

The normal spaces are the original global tangent spaces quotiented by
the derivatives of the actual curve inclusion. Differentiating the original
coordinate covering proves the genuine normal representation to have
characters `u⁻¹` and `u`, namely weights `-1` and `+1`, at every curve point.

These statements concern the action already constructed in the frozen
vertical-action package. They use neither a classification of global
vector fields nor an identification with `Aut⁰`.
-/
