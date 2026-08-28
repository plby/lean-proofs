import Wikipedia.HopfProblem.ConifoldPolarSmoothingBoundary
import Wikipedia.HopfProblem.ConifoldPolarRegions
import Wikipedia.HopfProblem.ConifoldPolarNativeCircle
import Wikipedia.HopfProblem.ConifoldPolarSmooth

/-!
# Explicit global coordinates for the standard conifold smoothing

This package proves, without assuming a polar-decomposition theorem, the
homeomorphism from the original determinant-one complex matrix group to
standard Euclidean three-space times the native unit three-sphere.  Its
positive factor is the literal matrix

`P = (N * N.conjTranspose + 1) / sqrt (frobeniusSq N + 2)`.

The unitary factor is `(N + adjugate (N.conjTranspose))` divided by the same
positive real denominator.  Its second column supplies the four unchanged
real normal coordinates.  The original right diagonal circle action fixes
the Euclidean three-coordinate and rotates the normal vector by the already
formalized native circle rotation.

Squared Frobenius sublevels correspond to closed Euclidean three-balls times
the three-sphere, with exact inverse matrix formulas and native compactness.
The existing standard conifold boundary map has its literal marked-frame
factorization in these coordinates.  Both ambient directions are real
analytic; the sphere-valued smooth interfaces use the pre-existing sphere
atlas and do not transport a new atlas onto the matrix group.

Composing with the explicit standard-six-sphere complement model identifies
this standard smoothing with that standard complement.  Nothing here asserts
that the actual constructed threefold complement is this matrix model, or
that the constructed threefold is a sphere.
-/
