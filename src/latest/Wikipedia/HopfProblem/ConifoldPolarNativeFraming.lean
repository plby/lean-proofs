import Wikipedia.HopfProblem.ConifoldPolarNativeFramingBoundary
import Wikipedia.HopfProblem.ConifoldPolarNativeFramingFirstPiece
import Wikipedia.HopfProblem.ConifoldPolarNativeFramingRegions
import Wikipedia.HopfProblem.ConifoldPolarNativeFramingSmooth

/-!
# The native marked smoothing boundary and standard sphere exterior

The existing normalized native boundary map has polar base radius `3/4`.
An explicit linear isometry changes those coordinates to the original
real-sphere frame, and the explicit positive factor `4 * sqrt 3 / 3`
sends that radius to the complement radius `sqrt 3` of the chosen standard
normal-radius-`1/2` tube.  The original normal three-sphere coordinate is
unchanged.

The corrected global model homeomorphism therefore agrees pointwise with
the original half-radius standard boundary map.  It restricts to a
homeomorphism from the literal determinant-one Frobenius sublevel
`frobeniusSq ≤ 17/4` onto the literal closed standard sphere exterior.
Smoothness is expressed using the unchanged source and target atlases,
with ambient matrix-valued maps; no manifold atlas is transported to the
matrix level set.

These are unconditional comparisons of the explicit standard models and
the already constructed native boundary.  They do not identify the
complement of the normal neighborhood in the original threefold with
the smoothing cap or with the standard sphere exterior.
-/
