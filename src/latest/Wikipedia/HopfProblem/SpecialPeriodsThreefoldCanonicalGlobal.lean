import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSections
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspPullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspScalar
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonDescentCovariance
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorIdentification
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalGenerator
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundle
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleOpenMapsResults
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleRefinement
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalMeromorphicDivisorOrders

/-!
# The genuine global canonical-bundle formula

This is the unconditional canonical-bundle formula of Proposition 9.11
for the constructed compact threefold.  The original native canonical
bundle is identified with the tensor product of the actual pulled-back
sphere ideal line `O(-infinity)` and the actual effective Cartier line
`O(2 S2)`:

* `Canonical.GlobalComparison.canonicalBundleBiholomorph` is a genuine
  holomorphic, base-preserving, complex-fibre-linear isomorphism;
* its source fibres are the full spaces of continuous alternating
  three-covectors on the actual tangent spaces;
* the base line is identified with the actual vanishing ideal on every
  chart subopen, and pullback and tensor use the genuine native bundles;
* the Cartier section has its proved double zero along the actual
  second elliptic fibre and its reduced pole along the cusp fibre;
* the actual normalized form `dt wedge e / F`, its elliptic extensions,
  and the cusp regularization agree through the proved local maps.

All overlap equalities are consequences of those actual section
identities and actual chart derivatives.  No gluing, divisor formula,
or canonical-bundle hypothesis is supplied.  The relative canonical
pushforward and the separate non-torsion conclusion are not asserted
by this package.
-/
