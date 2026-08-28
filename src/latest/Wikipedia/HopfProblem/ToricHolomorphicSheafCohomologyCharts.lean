import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyChartsToric
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyChartsIncidence

/-!
# Actual affine-chart holomorphic cohomology for the toric components

The product-to-native coordinate equivalence and the actual analytic
chart parametrizations transfer the proved affine vanishing to each
actual zero-ray chart open and to each actual incidence blow-up chart
open. Both finite covers retain their literal chart maps. All cohomology
groups are Mathlib's original `Sheaf.H` of the holomorphic function sheaf
on the actual open submanifold; no whole-surface acyclicity is inferred.
-/
