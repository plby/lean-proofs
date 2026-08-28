import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionNaturality
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionConstants

/-!
# Genuine cohomology comparison for the normalization resolution

An actual exact length-two augmented resolution is split into two actual
short exact sequences. Mathlib's Ext connecting maps identify its genuine
sheaf cohomology with the kernel, homology, and cokernel of the literal
global-section complex in degrees zero, one, and two. Termwise higher
acyclicity also gives vanishing above degree two. The low-degree formulas
retain the exact acyclicity hypotheses each uses.

The comparisons preserve actual connecting representatives and commute
with maps of augmented resolutions, including compatible scalar maps.
Both the actual holomorphic cusp resolution and the actual constant
resolution are packaged, together with their literal comparison map.

This is the generic homological comparison step. It does not assume or
claim analytic vanishing for the toric surface or its boundary curves,
nor does it define sheaf cohomology to be the displayed section complex.
-/
