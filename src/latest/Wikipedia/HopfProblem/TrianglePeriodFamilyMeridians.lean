import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansBasedTransport
import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansOfSphere

/-!
# Geometric meridians and the actual period-family monodromy

This package constructs small meridian loops in the actual regular
triangle quotient, not merely loops chosen to realize deck elements.

* At an elliptic point of order `m = 3` or `4`, the actual normalized
  Cayley lift is `r * exp(2πit/m)`.  Its genuine quotient chart is
  `r^m * exp(2πit)`.
* At the cusp, the actual lifted path is `z + width*t`.  The original
  exponential coordinate is `q(z) * exp(2πit)`.
* Both lifts stay in the actual regular locus.  Unique covering lifting
  verifies the whole paths and their inverse-generator endpoints.
* The clockwise reversals have phase `-2πt` and generator endpoints.
  Forward homology transport on the counterclockwise loops gives `A₁`,
  `A₂`, and `M₀`; inverse transport on the clockwise loops gives those
  same matrices, as required by the source's explicit Convention 3.17.

The homology statements concern actual singular first homology of the
literal fibres, in the proved period-column marking.  Attaching genuine
tails gives the corresponding statements in one common base fibre.  No
fundamental-group generating or product relation is claimed for arbitrary
chosen tails.

The general transport statements use a period map and its two generator
laws.  `Meridians.OfSphere` fills those inputs with the constructed
`Construction.periodMapOfSphere`; its only geometric input is the actual
normalized compact-quotient sphere equivalence, not any period map,
covariance, transport, endpoint, or meridian-existence hypothesis.
-/
