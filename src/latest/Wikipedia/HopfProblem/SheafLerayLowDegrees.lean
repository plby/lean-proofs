import Wikipedia.HopfProblem.SheafLerayLowDegreesSequenceNaturality
import Wikipedia.HopfProblem.SheafLerayLowDegreesScalars

/-!
# The unconditional native low-degree Leray sequence

For every continuous map `f : X ⟶ Y` and every abelian sheaf `F` on `X`,
`SheafLerayLowDegrees.lowDegree_exact` proves

`0 → H¹(Y, f_*F) → H¹(X, F) → H⁰(Y, R¹f_*F) → H²(Y, f_*F)`.

The cohomology groups are Mathlib's actual Ext-defined `Sheaf.H`, and
the higher direct image is its actual right-derived sheaf pushforward.
The maps come from the pushed-forward injective resolution and its
native cycle and boundary connecting morphisms.  No Leray exactness,
acyclicity, finiteness, or geometric hypothesis is assumed.

All three maps are natural in the coefficient sheaf.  A complex scalar
action by actual sheaf endomorphisms makes the same maps complex-linear;
the action on the higher direct image is induced by the native derived
functor.  The vanishing corollaries identify the original edge map with
an additive or complex-linear equivalence when the two actual outer
cohomology groups vanish.
-/
