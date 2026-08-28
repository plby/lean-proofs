import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassInjectivityKernel

/-!
# Injectivity of the actual two-function period-class map on every base open

The original two-function map into the actual neighborhood `Sheaf.H'`
is injective over the original ring of holomorphic base-open functions.
A zero neighborhood class has zero genuine global class on the original
restricted family; restricting to each of its actual fibres forces both
coefficient functions to vanish under the unchanged Dolbeault marking.

For four coefficient functions, the exact kernel consists of the actual
holomorphic linear period characters reconstructed from the last two
coefficients. Their genuine cocycles are coboundaries.

The proof assumes neither local generation nor a frame, and establishes
neither. All cohomology groups, complex atlases, and coefficient-induced
module actions remain the original ones.
-/
