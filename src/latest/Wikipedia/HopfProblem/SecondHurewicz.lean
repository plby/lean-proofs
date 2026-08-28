import Wikipedia.HopfProblem.SecondHurewiczNaturality

/-!
# The native second Hurewicz map and its structural laws

For every topological space and base point, `SecondHurewicz.hurewiczPi2`
maps Mathlib's actual `π_ 2 X x` to actual integral singular `H₂(X)`.
`SecondHurewicz.hurewiczMap` is the same map in integral-linear additive
notation. It has no connectedness or other topological hypotheses.

Its representatives are the original native cube maps applied to the
fixed square cross-product chain. Explicit singular three-chains prove
homotopy invariance and additivity. Naturality uses the actual induced
homotopy and singular-homology maps.

This package proves neither the second Hurewicz isomorphism theorem nor
any higher-homotopy, Whitehead, or smooth-sphere recognition theorem.
-/
