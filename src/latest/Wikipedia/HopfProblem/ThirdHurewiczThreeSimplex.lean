import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexHomology
import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionRecovery
import Wikipedia.HopfProblem.ThirdHurewiczFourSimplex

/-!
# Native three-simplex classes and their geometric relations

A singular three-simplex with its whole boundary at the base point defines
an element of Mathlib's native third homotopy group.  Its Hurewicz image is
the actual singular cycle consisting of that simplex minus the constant
simplex.  The cubical fundamental chain subdivides into the six original
oriented affine tetrahedra.  The native cube class has the same subdivision
when all its internal coordinate-equality faces are based.

The five actual faces of a singular four-simplex based on its geometric
two-skeleton satisfy the alternating relation in the same native group.
These facts use explicit relative homotopies and singular-chain identities;
they require no connectivity or homology-isomorphism hypothesis.
-/
