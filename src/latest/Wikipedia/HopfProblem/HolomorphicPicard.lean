import Wikipedia.HopfProblem.HolomorphicPicardGroup
import Wikipedia.HopfProblem.HolomorphicPicardNativeGauge
import Wikipedia.HopfProblem.HolomorphicPicardTensorCore
import Wikipedia.HopfProblem.HolomorphicPicardExt
import Wikipedia.HopfProblem.HolomorphicPicardCechExtension
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionEvaluation
import Wikipedia.HopfProblem.HolomorphicPicardCechClassInjectivity
import Wikipedia.HopfProblem.HolomorphicPicardCechRefinementDescent

/-!
# The genuine native holomorphic Picard group

The objects are original native holomorphic complex line bundles, and
their equivalence relation is actual analytic fibre-linear isomorphism.
Actual transition cocycles and genuine analytic gluing prove the bijective
classification by mathlib's derived first cohomology of the original sheaf
of holomorphic units. Tensor product, dualization, and the trivial bundle
are constructed from the original native transitions, independently of
cohomology; their original fibre tensor/dual interpretations hold in every
native chart. These operations give the actual isomorphism-class quotient
an abelian group structure and the classification an additive equivalence.

The main endpoint is `LineBundle.classificationAddEquiv`. Its forward map
is definitionally the already constructed genuine native cocycle class.
Vanishing of that class is equivalent to an actual native analytic
trivialization, and the group laws yield actual analytic isomorphisms of
the constructed tensor and dual bundles.

Supporting results construct actual short exact extension representatives,
prove the degree-one Čech-to-derived comparison and its additivity,
identify analytic bundle isomorphisms with genuine coboundaries, and
establish the original-chart recovery and tensor/dual formulas. No Čech
comparison, classification, acyclicity, or geometric trivialization premise
is imposed. This general classification does not compute the Picard group
of the particular threefold without its separate cohomology calculations.
-/
