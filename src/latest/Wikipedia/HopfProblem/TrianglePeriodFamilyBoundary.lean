import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryColumnEvaluation
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticSourceProjection
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticTopWang
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryFibreTransportNaturality
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryRadiusMonodromy

/-!
# Actual fibre transport and elliptic boundary homology

This package compares the original elliptic cap-boundary maps with the
fixed actual slit cover of the regular period family.  The comparison
uses the original logarithmic gauge, genuine whole-boundary homotopies,
actual covering lifts and their tail frames, and naturality of the actual
singular Mayer--Vietoris connecting maps.

The resulting `ellipticThreeBoundary_sourceKernelProjection` and
`ellipticFourBoundary_sourceKernelProjection` identify the respective
source-kernel coordinates with the actual Wang boundary in every degree.
The degree-five boundary marking is itself the actual Wang map followed
by the actual integral fourth-homology marking of the fibre torus.

Actual fibre transport and arbitrary small-radius meridian comparisons
are included.  This package does not assert a numerical full boundary
matrix in a noncanonical splitting, or evaluate the cusp boundary column.
-/
