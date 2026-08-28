import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspRegular
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticPaths
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticCap
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusEllipticHomotopy
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusSections
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusHomology

/-!
# Mapping-torus models for the three genuine filling overlaps

Each literal overlap between the regular special-period family and a filling
is homotopy equivalent to the mapping torus of its actual affine period-torus
monodromy.  The underlying punctured families are identified with a radial
interval times that mapping torus using their original quotient topologies.

The imported representative formulas retain the genuine logarithmic gauge
at the two elliptic points and the original real period coordinates at the
cusp.  Both boundary maps are the original overlap inclusions composed with
the inverse homotopy equivalence.  Their induced maps on integral singular
homology therefore give the literal coefficients in the attachment sequence.
Changing an elliptic boundary's radius and phase is accompanied by an explicit
homotopy in the original punctured piece, preserving both coefficient maps.
-/
