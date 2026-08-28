import Wikipedia.HopfProblem.HolomorphicPicardExtPullback
import Wikipedia.HopfProblem.HolomorphicPicardExtRepresentation
import Wikipedia.HopfProblem.HolomorphicPicardExtSplit
import Wikipedia.HopfProblem.HolomorphicPicardExtEquivalence
import Wikipedia.HopfProblem.HolomorphicPicardExtIntegerOne
import Wikipedia.HopfProblem.HolomorphicPicardExtIntegerOneNormalization
import Wikipedia.HopfProblem.HolomorphicPicardExtLocalCocycle

/-!
# Genuine extension representatives of Ext and native sheaf `H¹`

Every degree-one Ext class in an abelian category with enough injectives
has an actual short exact representative.  Its class is zero exactly
when the extension splits; two extensions with the same endpoints have
equal classes exactly when an isomorphism fixes both endpoints.

For native sheaf cohomology, actual local lifts of the integer section
`1` yield genuine overlap cocycles, with their sign convention recorded.
-/
