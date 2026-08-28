import Wikipedia.HopfProblem.FourthHurewiczIso
import Wikipedia.HopfProblem.FourthHurewiczNaturality
import Wikipedia.HopfProblem.FourthHurewiczFourSimplex
import Wikipedia.HopfProblem.FourthHurewiczThreeSimplexNullhomotopy

/-!
# The original native fourth Hurewicz isomorphism

This package constructs the actual cubical map from Mathlib's native
fourth homotopy group to integral singular homology. Under actual simple
connectedness and vanishing of the native second and third homotopy
groups, geometric simplex contraction and signed cubical subdivision
give a constructed inverse. Both inverse identities retain the original
map and the original boundary-relative generalized-loop quotient.

The supporting simplex nullhomotopies, cube pasting, native subdivision,
and native signed face relation work in arbitrary dimensions. No higher
Hurewicz theorem, Whitehead theorem, or sphere recognition is an input.
-/
