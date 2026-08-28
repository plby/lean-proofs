import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundle
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalNonTorsion

/-!
# Canonical powers, pluricanonical vanishing, and non-torsion

This package proves the canonical-power and non-torsion consequences
of Proposition 9.11 for the actual constructed compact threefold:

* the tensor square of the actual Cartier line of `2 S2` is genuinely
  holomorphically isomorphic to the pulled-back point line at one;
* `Canonical.Powers.canonicalSquareBiholomorph` identifies the genuine
  canonical square with the actual pullback of the sphere ideal line
  `O(-infinity)`, and its fourth power with `f* O(-2 infinity)`;
* all positive native pluricanonical section spaces vanish, hence all
  positive plurigenera are zero;
* no positive tensor power admits an actual holomorphic fibre-linear
  product trivialization, so the canonical bundle is non-torsion.

All powers have full tensor-fibre identifications with the original
canonical fibres and the actual intrinsic alternating three-covectors.
The isomorphisms use the literal quartic elliptic equation, holomorphic
unit ratios, actual native bundle maps, and their proved overlaps.
Vanishing uses genuine dual evaluation, the compact scalar maximum
principle, and the actual dense complement of the cusp fibre.  No
relative-duality, section-descent, or Grauert hypothesis is supplied.

The separate identification and degree of the relative canonical
pushforward are not asserted by this package.
-/
