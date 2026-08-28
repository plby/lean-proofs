import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductSectionWang

/-!
# The genuine cap-adapted boundary coordinates and their marked section

The actual elliptic boundary is the original central surface times a circle,
and the original filling map is the first projection on every homology class.
The actual section of this projection has its signed Wang image computed in
the source's unchanged exterior-cube marking.  These statements do not use
an arbitrary projective splitting of the regular family's homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct

open Elliptic Elliptic.HigherHomology SpecialPeriods SpecialPeriods.EllipticFilling
open SingularMayerVietoris MappingTorusHomology ThreefoldOverlapMappingTorus
open SpecialPeriods.Threefold.Homology.Finiteness

/-- The actual section image of the original central surface's marked unit top class. -/
def unitCapSectionClass (j : Kind) :
    SingularHomology (ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j) 4 :=
  singularHomologyMap (capSection j) 4
    ((surfaceH4Equiv j (specialLocalData j).centralPeriod).symm 1)

/-- Its genuine cap-adapted coordinates are the first integral unit axis. -/
theorem unitCapSectionClass_coordinates (j : Kind) :
    boundaryCapH4Equiv j (unitCapSectionClass j) = (1, 0) := by
  rw [unitCapSectionClass, boundaryCapH4Equiv_section, LinearEquiv.apply_symm_apply]

/-- The literal original filling coefficient takes this actual boundary class
to the original marked cap orientation class. -/
theorem unitCapSectionClass_filling (j : Kind) :
    surfaceH4Equiv j (specialLocalData j).centralPeriod
      (ellipticPieceRetractionHomologyEquiv j 4
        (boundaryFillingHomologyMap (some j) 4 (unitCapSectionClass j))) = 1 := by
  rw [boundaryFillingHomologyMap_H4_first, unitCapSectionClass_coordinates]

/-- Its actual signed Wang coordinate is minus the common `uwδ` unit axis. -/
theorem unitCapSectionClass_wang (j : Kind) :
    FlatTorus.singularH3Coordinates
      (wangBoundary (flatTorusAffine j j.twist) 3 (unitCapSectionClass j)) =
        -Pi.single (3 : Fin 4) 1 :=
  capSection_wang_h4_unit j

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapProduct
