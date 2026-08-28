import Wikipedia.HopfProblem.PeriodTorusLineBundleChernEtaCupSquare
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernClassOperationsTensor
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativeFrameBoundary
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernTransitions
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernWindingOperations
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernWindingMultiplicative
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernLog

/-!
# Genuine integral Chern classes of native period-torus factor bundles

The construction starts with actual nonzero native edge sections and a
true continuous, fibre-linear frame on each lifted singular simplex.
Their boundary winding defines a literal closed singular two-cochain.
Its comparison with the integer exponential cocycle is proved, including
the sign fixed by the positive lattice action and inverse frame changes.

For the original first-linear Hermitian Appell--Humbert convention,
`c₁(integralFactor E) = -coefficientClass E`.  The actual factor for `-E`
therefore realizes the positive native class.  In particular the actual
native bundle `etaChernFactor p n` has Chern class `nη`.  The distinguished
class at `n = 1` has genuine singular cup square twelve on the positive
real period product.

The package also proves native analytic bundle-isomorphism invariance,
explicit singular coboundary corrections, factor-product additivity and
compatibility with the constructed canonical fibre-tensor equivalences.
Compatible-linear native pullback is provided by the separate pullback
leaf.  No arbitrary-bundle classification, Néron--Severi identification,
Poincaré duality, or comparison with complex orientation is assumed.
-/
