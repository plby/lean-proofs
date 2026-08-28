import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticFibres
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticNormalBundle
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticNormalFibre
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticRetractionHomology

/-!
# Actual elliptic geometry of the unconditional compact threefold

This entry collects the genuine geometry of the two elliptic fibres of
the constructed sphere projection:

* the native finite affine quotient surfaces are biholomorphic to the
  literal fibres over zero and one;
* the selected fibre charts are full restrictions of actual ambient
  immersion charts, in both coordinate directions;
* the projection is the third or fourth power of a transverse coordinate
  in genuine analytic charts of the existing global atlas;
* the actual normal tangent quotients, including those of the literal
  fibre inclusions, identify with the proved geometric character lines;
  their least positive trivial tensor powers have orders three and four;
* each original chosen elliptic piece and its entire global lifted patch
  strongly deformation retract onto its actual central surface, and the
  inclusion induces the proved fundamental-group and integral singular
  first-homology isomorphisms.

The local homology statements concern these full elliptic patches, not
the entire compact threefold. No existence of periods, fillings,
uniformization, gluing, local comparisons, or resulting geometry is an
input to this package.
-/
