import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangKernel

/-!
# Actual elliptic cap-kernel Wang maps in boundary degrees two and three

This package computes the actual Wang boundary on the inverse of the
original cap-kernel isomorphism.  Its input is the genuine positive-circle
summand of the native boundary-to-surface product homeomorphism.

The proof uses the literal finite-covering square, invariance of genuine
singular cross products under its circle shear, and the actual affine
monodromy norm.  The output uses the original rank-four period marking
and its ordered exterior-square marking.  The existing surface markings
are unchanged: their actual covering shears occur explicitly in the
formulas and exact image lattices.

The main endpoints are `capKernel_wang_h1_coordinates`,
`capKernel_wang_h2_coordinates`, `h1Coordinates_range`, and
`h2Coordinates_range` in
`TrianglePeriodFamily.Boundary.EllipticCapKernelWang`.
-/
