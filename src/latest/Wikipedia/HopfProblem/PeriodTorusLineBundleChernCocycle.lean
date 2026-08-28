import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleClass

/-!
# Native singular classes from integral group and geometric edge cocycles

This package constructs an actual integral singular two-cochain from an
integral additive-group two-cocycle and labels on actual singular edges
satisfying the triangle identity. Its closedness follows from genuine
tetrahedron faces. The resulting native cohomology class is additive,
natural under continuous pullback, and unchanged by group coboundaries.

The fixed convention is `c(σ) = k(label 01, label 12)` and the incoming
singular boundary is `12 - 02 + 01`. No identity normalization, replacement
cohomology object, Čech comparison, or Chern-class identification is assumed.
-/
