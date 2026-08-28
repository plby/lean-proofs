import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedIso
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangle

/-!
# The genuine degree-two Hurewicz theorem

For `[TopologicalSpace X] [SimplyConnectedSpace X]` and `x : X`,
`SecondHurewicz.SimplyConnected.hurewiczPi2_bijective x` proves bijectivity
of the previously constructed map on Mathlib's native second homotopy
group and actual integral singular homology. The corresponding group and
integral linear equivalences have that same map as their forward map.

The proof uses actual paths, simplex homotopy extension, coherent face
straightening, singular prism chains, native square homotopies, and the
signed tetrahedron relation. No CW, separation, manifold, higher Hurewicz,
Whitehead, or sphere-recognition hypothesis is an input.
-/
