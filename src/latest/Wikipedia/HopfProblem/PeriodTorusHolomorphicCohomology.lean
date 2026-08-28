import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDimensions
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierTop
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyNativeConnecting

/-!
# Actual holomorphic sheaf cohomology of every native period torus

For every original `p : PeriodDomain`, Mathlib's actual Ext-defined
cohomology of the original holomorphic-function sheaf is complex-linearly
ℂ, ℂ², ℂ in degrees zero, one, two and zero in higher degrees. The scalar
action is induced by multiplication on that original sheaf. The groups
are genuinely finite-dimensional, with dimensions `Nat.choose 2 q` and
Euler characteristic zero.

The proof constructs and proves exact an actual Dolbeault resolution
on all opens of the unchanged quotient atlas. Smooth partitions prove
its terms acyclic. The genuine global-section complex is identified
with smooth marked-torus Fourier coefficients. Constructed primitives
then identify its actual homology and cokernel by probability Haar means.
The coordinate classes agree with the original Ext connecting maps;
literal constant coefficients supply the inverse comparisons.

No generic-period, local-solvability, acyclicity, Dolbeault-comparison,
or cohomology-dimension premise is assumed. This fibre computation does
not assert a family base-change or higher-direct-image theorem.
-/
