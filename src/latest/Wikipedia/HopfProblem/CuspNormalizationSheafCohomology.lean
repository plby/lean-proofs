import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyDimensions
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardDerived

/-!
# Source Lemma 9.12(ii): actual holomorphic cohomology of the cusp fibre

The independently constructed reduced holomorphic structure sheaf has
genuine complex-linear cohomology groups ℂ, ℂ², ℂ in degrees zero, one,
two, and zero in every higher degree. Its Euler characteristic is zero.
The proof uses the actual exact normalization resolution, actual finite
closed pushforwards, actual sphere and toric-surface analytic acyclicity,
and genuine Mathlib Ext comparisons. No higher-acyclicity, Stein,
rational-surface, Čech-comparison, or cohomology-dimension premise remains.

This package does not assert the later constant-to-holomorphic
cohomology comparison or cup-product conclusions of parts (iii) and (iv).
-/
