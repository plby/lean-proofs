import Wikipedia.HopfProblem.HolomorphicCharacterBundleCriterion
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreCriterion
import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedCoreIdentification
import Wikipedia.HopfProblem.HolomorphicCharacterBundleAssociatedCoreTensor

/-!
# Holomorphic character line bundles (Lemma 5.7(ii))

This package constructs both the actual associated quotient `(A × ℂ)/G` and
the analytic `VectorBundleCore` of its character cocycle, and identifies the
two by an explicit analytic fibre-linear isomorphism. All atlases and
topologies are those of the independently constructed quotient and bundle.

For compact connected complex `A`, an actual holomorphic linear
trivialization exists if and only if the character is trivial. The proof
passes through genuine holomorphic sections, whose pulled-back scalar
functions are holomorphic and character-equivariant. Character products
are verified to be tensor products in the local charts, and the least
positive trivial character power is the character's exact order.

The finite-action specialization constructs the covering of the actual orbit
quotient from a finite free holomorphic action. No assertion here identifies
a canonical or normal bundle of a particular elliptic surface with one of
these character bundles; those identifications require their own geometry.
-/
