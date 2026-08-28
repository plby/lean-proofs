import Wikipedia.HopfProblem.SphereHomologyCoefficientsSphere
import Wikipedia.HopfProblem.SphereHomologyCoefficientsNaturality

/-!
# Native finite-coefficient singular homology of positive-dimensional Euclidean spheres

The coefficient object is Mathlib's `ModuleCat.of ℤ (ZMod p)`. The actual
short exact coefficient chain sequence gives the Bockstein sequence and
the scalar-quotient comparison when the preceding integral homology is
torsion-free. Coefficient reduction is natural for genuine continuous maps.

Applying these constructions to the proved integral sphere homology gives
`ZMod p` in degree zero and the sphere dimension, and zero in all other
degrees, for every nonzero modulus. The positive point and actual singular
suspension top classes reduce to the specified coefficient generators.
-/
