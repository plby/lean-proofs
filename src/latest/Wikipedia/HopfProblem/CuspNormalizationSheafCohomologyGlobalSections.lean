import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsForgetLinear
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsRepresentatives

/-!
# Global sections of the actual cusp normalization resolution

The actual compact connected normalization component and the three actual
sphere curves have only constant holomorphic global functions. Together
with the genuine finite direct-image and skyscraper section comparisons,
this gives complex-linear identifications of the actual resolution terms
with ℂ, ℂ³, and ℂ². The actual first global arrow is zero; the actual last
arrow is `(a₀,a₁,a₂) ↦ (a₀-a₁+a₂,a₀-a₁+a₂)`, in the source's P/Q order.

The kernel, actual categorical homology, and cokernel of this global
complex have dimensions 1, 2, and 1. Their representatives and the
canonical comparisons with the abelian-group global complex used by the
Ext-defined resolution theorem are retained. No higher-cohomology
vanishing is assumed here, and these results alone are not asserted to
compute the higher cohomology of the reduced structure sheaf.
-/
