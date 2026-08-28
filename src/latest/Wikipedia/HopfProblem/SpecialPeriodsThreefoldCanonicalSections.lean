import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonical
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsPatchTriviality
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsPatchesOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsSpecialOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsUnitLog

/-!
# Actual ambient canonical sections and their elliptic zero orders

This module establishes the section and zero-order assertions of source
Lemma 9.10(ii) for the unconditionally constructed special period map.

* `SectionsUnit.periodUnit` is an explicit nowhere-zero holomorphic unit
  correcting the actual finite generator's three-dimensional Jacobian.
  `SectionsUnit.unitLog` is its explicit holomorphic exponent, giving
  literally the source's coefficient `s^k exp(φ(s))` on the whole disc.
* `Canonical.Sections.fullHolomorphicSection` is a genuine section of the
  native ambient canonical bundle of each original full elliptic filling.
  Its actual quotient-differential pullback is the corrected upstairs
  three-form, invariant under the entire finite cyclic action.
* `Canonical.Sections.fullSection_native_unit_factor` gives the actual
  native-chart factorization as a transverse coordinate to power zero or
  two times a holomorphic nowhere-zero unit and the actual volume frame.
* `Canonical.Sections.fullTransverseCoefficient_analyticOrderAt` measures
  the actual section coefficient along the actual native transverse chart
  line, at every point of the reduced central fibre.  Its order is exactly
  zero in the first filling and two in the second.
* The first section is nowhere zero.  The second has no zeros outside its
  actual central surface.  `fullThreeTrivialization` is an actual
  holomorphic, fibrewise-linear trivialization of the first ambient
  canonical bundle, with inverse given by scalar multiplication of that
  section.
* `Canonical.Sections.patchSection` and `patchSectionMap_holomorphic`
  transport the sections to the entire actual global elliptic patches by
  the previously proved differential-pullback bundle biholomorphisms.
  The second patch section vanishes exactly over the sphere value one.
  `firstPatchTrivialization` gives the actual product trivialization of
  the global canonical bundle on the entire first patch, with inverse
  scalar multiplication by the transported section.
  `patchTransverseCoefficient_analyticOrderAt` proves the same exact zero
  orders in actual glued charts, along their literal inverse-chart lines.

The original signed cusp volume and its nowhere-zero holomorphic global
patch section are included by the native canonical-bundle import.  These
are ambient threefold statements, distinct from the canonical bundles of
the central surfaces.  No global canonical divisor formula or isomorphism
with a divisor-labelled line bundle is asserted here.
-/
