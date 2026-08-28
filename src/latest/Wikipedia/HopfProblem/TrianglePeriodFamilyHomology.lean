import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebraDifferences
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyCanonical
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySectionConnected
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySectionRestriction

/-!
# Actual singular homology of the regular special-period family

This package supplies the regular-family part of the source's homology
calculation from genuine topology and integral singular chains.

* The two actual slit domains have covering sections, real-torus family
  charts, and three actual overlap components. Their transition elements
  are identified using the previously constructed geometric meridians.
* The actual singular Mayer--Vietoris sequence is normalized by explicit
  integral row and column operations. The result is a short exact sequence
  with actual family homology in the middle and actual monodromy-difference
  cokernel and kernel at the ends.
* The integral period markings identify the actual differences with the
  source matrices and their exterior powers. Their exact integer images
  and kernels give the free endpoints without rationalization.
* Projectivity of the proved free kernel gives an integral splitting. This
  produces actual homology ranks `1, 3, 6, 8, 6, 2`, vanishing above degree
  five, and torsion-freeness in every degree.
* The first coordinate is the positive literal fibre-inclusion map. The
  remaining coordinates retain the actual connecting projection; only its
  chosen linear section is noncanonical.

`TrianglePeriodFamily.Canonical.specialRegularHomologyEquiv` and the
accompanying exact-sequence and fibre-map statements specialize all inputs
to the constructed special regular family. No homology conclusion for the
later compact threefold, or coordinate formula for a filling-boundary map,
is asserted merely from this regular-family result.
-/
