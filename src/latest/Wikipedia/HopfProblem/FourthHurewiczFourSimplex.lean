import Wikipedia.HopfProblem.FourthHurewiczFourSimplexHomology
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionRecovery
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativePermutationInsertionRecursion
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplex

/-!
# Native four-simplex classes and their geometric relations

An actual singular four-simplex with its entire boundary based defines a
class in Mathlib's native fourth homotopy group.  Its fourth Hurewicz image
is the actual cycle consisting of the original simplex minus the constant
four-simplex.  The original recursive cube chain is the signed sum of its
twenty-four affine permutation simplices.

When the internal coordinate-equality faces are based, the native cube
class has the corresponding signed subdivision.  The six actual faces
of a five-simplex based on its geometric three-skeleton satisfy the
alternating relation in the same native group.  The quotient, native
subdivision, and boundary-relation arguments are dimension-generic.
-/
