import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochains
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSmallCochainComparison
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheaf
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonNormalization
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonIntegralCoefficientExt
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLinearComparison

/-!
# Genuine constant-sheaf and singular cohomology comparison

The original constant sheaf's native Ext cohomology in degrees one and
two is canonically isomorphic to the actual singular cohomology with
arbitrary abelian coefficients on compact Hausdorff locally contractible
spaces. The comparison uses the genuine augmented singular cochain
sheaf resolution, its proved Ext acyclicity, and the actual global
sheafification unit's proved cohomology isomorphism.

The original integral and complex coefficient objects and maps are
retained, including `ℤ → ℂ` and their actual complex scalar actions.
The comparison is natural for genuine finite closed pullbacks; in
particular, the manuscript's original normalization map and its literal
degree-two kernel are identified with their singular counterparts.
Concrete endpoints apply to the original normalization component,
Riemann sphere, cusp central fibre, and threefold.

Multiplicativity with the singular cup product is a separate theorem,
not an assumption or assertion of this comparison package.
-/
