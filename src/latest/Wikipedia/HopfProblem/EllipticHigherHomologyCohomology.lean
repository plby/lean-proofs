import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyMaps
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyProperties
import Wikipedia.HopfProblem.EllipticHigherHomologySpecialCohomology

/-!
# Native integral singular cohomology of the elliptic fillings

This leaf assembles the cohomology of the actual singular cochain
complexes for the mapping tori, central surfaces, full fillings and
literal special reduced fibres.  Their integral cohomology is finite
free with ranks `(1,2,2,2,1,0,...)`, in every degree.

The coordinates are defined through the proved canonical evaluation
isomorphism, with its homology-projectivity requirement discharged by
the previously constructed actual homology bases.  The central-inclusion
pullback and the radial-retraction pullback are proved to be inverse
isomorphisms preserving these coordinates.  The finite period-torus
covering and the literal map into the filling satisfy the actual
evaluation and pullback naturality formulas.

No cohomology group is defined as a homology dual, no desired
universal-coefficient assertion is assumed, and no numerical covering
matrix is substituted for the actual continuous covering map.
-/
