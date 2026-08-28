import Wikipedia.HopfProblem.SheafCupProductCoface
import Wikipedia.HopfProblem.SheafCupProductNativeExterior
import Wikipedia.HopfProblem.SheafCupProductFunctionsLinear
import Wikipedia.HopfProblem.SheafCupProductCuspLinear

/-!
# Genuine low-degree cup products on native sheaf cohomology

The actual multiplicative Godement construction gives a ring-sheaf
partial resolution. Original stalk contractions prove its exactness,
and actual complex scalars prove injectivity of its first two additive
terms. The genuine Ext comparison therefore identifies Mathlib's native
H¹ and H² with the original Godement cocycle quotients.

The literal Alexander--Whitney product induces an alternating,
complex-bilinear native H¹ × H¹ → H² product and its genuine exterior-square
factor. Original coefficient maps preserve these products. Constant,
holomorphic, and reduced holomorphic sheaves carry their actual scalar
actions, not vector-space structures assigned through a dimension result.

On the actual cusp, constant cups lie in the original normalization H²
kernel. The already proved original constant-to-holomorphic edge
isomorphism sends them to the actual holomorphic cups. This package does
not assert a singular-cup comparison, nonvanishing, or an exterior-square
isomorphism.
-/
