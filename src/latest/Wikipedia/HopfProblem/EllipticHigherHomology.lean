import Wikipedia.HopfProblem.EllipticHigherHomologySpecialProperties
import Wikipedia.HopfProblem.EllipticHigherHomologySurfaceMarked
import Wikipedia.HopfProblem.EllipticHigherHomologyHomologyNorm

/-!
# Actual integral homology of the elliptic central surfaces and fillings

This package proves the full integral singular homology profile
`(ℤ, ℤ², ℤ², ℤ², ℤ, 0, …)` for the actual elliptic central surfaces
with the source's main twists.  The same profile holds for their literal
reduced fibres and entire actual special fillings.  All groups are free
and finitely generated, and the actual Euler sum is zero.

The proof constructs an explicit homeomorphism to a mapping torus of
the actual inverse three-torus monodromy.  The genuine singular Wang
sequence and marked integral torus homology then give the actual groups.
The genuine central inclusion and the original finite period-torus
covering maps are retained, including their primitive fibre axes.

The finite homology-norm matrices and their invariant coordinates are
also calculated for the actual induced fibre maps.  Identifying the
remaining covering coordinates requires a separate cyclic-cover Wang
naturality theorem; this package does not assume that identification.
-/
