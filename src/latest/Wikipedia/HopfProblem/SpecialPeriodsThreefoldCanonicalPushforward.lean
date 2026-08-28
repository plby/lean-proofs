import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardAbsolute
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeNormalized
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionComparison
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardLocalIso

/-!
# Native canonical direct images on the actual compact threefold

For the actual sphere projection, the original alternating-cotangent
canonical section sheaf has direct image the literal ideal O(-infinity).
The native relative canonical tensor bundle has direct image the dual
ideal line O(+infinity). Both comparisons are actual sheaf isomorphisms,
with O(U)-linear section equivalences on every full inverse image and
compatibility with every restriction.

The relative construction uses the unchanged native sphere cotangent
Hom bundle, its genuine reciprocal-chart derivative, and the full
intrinsic tensor fibre. Its projection formula is proved by actual
native contraction and sheaf gluing. No cohomological or base-change
theorem is supplied as an assumption.

The positive line is geometrically identified by its actual global
holomorphic section: native coefficients 1 and w, with a single simple
zero at infinity. This is a genuine Cartier comparison, not a degree
attached to a formally named line.

The normalized relative section maps to this very section. At every
finite base point its value in the original full tensor fibre is
exactly the original normalized Omega tensored with the genuine dual
finite-coordinate differential, including on the elliptic zero fibre.
-/
