import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionFamily
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionEmbeddingCohomologyComposition
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionNestedCohomology

/-!
# Actual native cohomology maps for original nested opens

Restriction along an actual open embedding is an exact functor of the
original additive sheaves. Its genuine constant integer endpoint defines
the original Ext map; the actual identity and composition isomorphisms
give identity and composition in degree one. For nested original opens,
the genuine free-open representing units identify this map with the
original cohomology-presheaf restriction under the native open comparisons.

Together with the actual open Čech-class and period-family comparisons,
this gives the native restriction framework without a cohomology or
functoriality premise. The family-specific coefficient formula remains
proved here for globally defined coefficients and constants; no local
frame or arbitrary-intermediate-open coefficient formula is asserted.
-/
