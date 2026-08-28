import Wikipedia.HopfProblem.SixthHurewiczIsoNaturality
import Wikipedia.HopfProblem.SixthHurewiczSixSimplex

/-!
# The original native sixth Hurewicz isomorphism

This package constructs the actual cubical map from Mathlib's native
sixth homotopy group to integral singular homology. Under actual simple
connectedness and vanishing of the native second through fifth homotopy
groups, geometric simplex contraction and signed cubical subdivision
give a constructed inverse. Both inverse identities retain the original
map and the original boundary-relative generalized-loop quotient. The
forward equivalence and its constructed inverse commute with induced maps.

The proof reuses the all-dimensional simplex nullhomotopies, cube pasting,
native subdivision, signed face relation, and corrected-cycle assignment.
The original recursive six-cube chain has its actual 720-cell expansion.
No higher Hurewicz theorem, Whitehead theorem, or sphere recognition is
an input.
-/
