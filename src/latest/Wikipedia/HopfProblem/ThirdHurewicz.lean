import Wikipedia.HopfProblem.ThirdHurewiczIso
import Wikipedia.HopfProblem.ThirdHurewiczNaturality
import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplex

/-!
# The genuine native third Hurewicz theorem

`ThirdHurewicz.hurewiczPi3` is the actual native cubical third Hurewicz
homomorphism to the original integral singular homology, with genuine
homotopy invariance, group law, and naturality.

For `[SimplyConnectedSpace X]`, `x : X`, and
`[Subsingleton (π_ 2 X x)]`, `ThirdHurewicz.hurewiczPi3_bijective x`
proves this same map bijective. The group and integral linear equivalences
have the original map as forward map and actual normalized-chain descent
as inverse. The proof uses native six-tetrahedron subdivision, the signed
five-face relation, genuine coherent simplex homotopies, and actual prism
boundaries. No higher Hurewicz, Whitehead, CW, manifold, separation, or
sphere-recognition hypothesis is assumed.
-/
