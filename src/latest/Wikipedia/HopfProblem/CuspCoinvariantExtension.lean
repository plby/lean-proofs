import Wikipedia.HopfProblem.CuspCoinvariantExtensionSpecial
import Wikipedia.HopfProblem.CuspCoinvariantExtensionPunctured

/-!
# A genuine collar-adjusted gamma map on the original cusp cap

`CuspCoinvariantExtension.collarExtension` constructs a continuous map on
the entire original cusp quotient.  It is invariant under the original
real delta flow, has the marked central value, and agrees exactly with
the original gamma coordinate outside an arbitrarily small positive
inner radius.  `specialCapGamma` specializes this to the actual cusp
piece of the threefold and retains the original regular gluing and global
circle-orbit comparisons.

The punctured gamma coordinate is not asserted to extend unchanged near
the central fibre.  The modified map is not asserted to be smooth, a
submersion, a product coordinate, or part of a sphere recognition theorem.
-/
