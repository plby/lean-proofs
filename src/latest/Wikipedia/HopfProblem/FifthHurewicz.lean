import Wikipedia.HopfProblem.FifthHurewiczIso
import Wikipedia.HopfProblem.FifthHurewiczNaturality
import Wikipedia.HopfProblem.FifthHurewiczFiveSimplex

/-!
# The original native fifth Hurewicz isomorphism

This package constructs the actual cubical map from Mathlib's native
fifth homotopy group to integral singular homology. Under actual simple
connectedness and vanishing of the native second, third, and fourth
homotopy groups, geometric simplex contraction and signed cubical
subdivision give a constructed inverse. Both inverse identities retain
the original map and the original boundary-relative generalized-loop
quotient.

The proof reuses the all-dimensional simplex nullhomotopies, cube pasting,
native subdivision, and signed face relation. The constant-five-simplex
correction is an actual six-boundary. No higher Hurewicz theorem,
Whitehead theorem, or sphere recognition is an input.
-/
