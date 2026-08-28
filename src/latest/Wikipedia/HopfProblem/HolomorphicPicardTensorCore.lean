import Wikipedia.HopfProblem.HolomorphicPicardTensorCoreTensor
import Wikipedia.HopfProblem.HolomorphicPicardTensorCoreDual
import Wikipedia.HopfProblem.HolomorphicPicardTensorCoreTrivial

/-!
# Tensor, dual, and unit interpretations for native cocycle bundles

For arbitrary actual unit-valued Čech cocycles on an actual open cover,
addition multiplies the native transitions.  The sum-cocycle native fibre
is linearly equivalent to the genuine tensor product of the two original
fibres, compatibly with the full linear transitions and every original
local trivialization.  Negation similarly gives the algebraic dual, with
the original evaluation pairing and contragredient transitions.

The zero cocycle has an actual analytic diffeomorphism to the Cartesian
product and an analytic fibre-linear isomorphism to mathlib's genuine
trivial line bundle, on the original native topologies and atlases.

The tensor and dual results here are fibrewise linear identifications
with proved chart compatibility.  No separate topology on a total space
of algebraic tensor or dual fibres is introduced or identified, and no
Picard group or sheaf-cohomology classification is assumed or defined.
-/
