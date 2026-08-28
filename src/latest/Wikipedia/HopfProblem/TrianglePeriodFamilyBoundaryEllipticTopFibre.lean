import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticTopFibreCoordinates
import Wikipedia.HopfProblem.ThreefoldHomologyEllipticFibre

/-!
# Signed actual top fibre-to-cap coefficients

The literal period cover acts by the actual covering norm after the
signed circle-boundary coordinate.  The preceding coordinate comparison
fixes that sign in the common original ordered four-period basis.  Thus
the original order-three and order-four fibre inclusions have coefficients
`3` and `-4` in the already fixed central-surface top markings.

These are equalities of the actual attachment maps after the actual cap
retraction.  They do not replace a finite-cover index with an assumed
signed degree, nor choose a new regular-family homology splitting.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticTopFibre

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods SpecialPeriods.EllipticFilling
open SpecialPeriods.Threefold.Homology.Finiteness
open SpecialPeriods.Threefold.Homology.EllipticFibre
open ThreefoldOverlapMappingTorus

/-- The actual real-period finite cover has its signed order as top coefficient. -/
theorem centralRealCover_h4_coordinates (j : Kind) (a : SingularHomology RealTorus₄ 4) :
    surfaceH4Equiv j (specialLocalData j).centralPeriod
        (singularHomologyMap (centralRealCover j) 4 a) =
      (j.order : ℤ) * γ j.twist * realTorusH4Equiv a := by
  rw [centralRealCover, singularHomologyMap_comp, LinearMap.comp_apply]
  change surfacePeriodCoverH4Coordinates j (specialLocalData j).centralPeriod
    (homeomorphHomologyEquiv
      (flatTorusPeriodHomeomorph (specialLocalData j).centralPeriod.val) 4 a) = _
  rw [surfacePeriodCoverH4Coordinates_apply, surfacePeriodCoverCircleBoundary_flat]
  ring

/-- The same coefficient for the literal original fibre inclusion into
the actual small filling, followed by its actual central retraction. -/
theorem fibreToFilling_h4_coordinates (j : Kind) (a : SingularHomology RealTorus₄ 4) :
    surfaceH4Equiv j (specialLocalData j).centralPeriod
        (ellipticPieceRetractionHomologyEquiv j 4
          (singularHomologyMap (fibreToFilling (some j)) 4 a)) =
      (j.order : ℤ) * γ j.twist * realTorusH4Equiv a := by
  have h := LinearMap.congr_fun (fibreToFilling_homology_retraction j 4) a
  change ellipticPieceRetractionHomologyEquiv j 4
    (singularHomologyMap (fibreToFilling (some j)) 4 a) =
      singularHomologyMap
        (periodCover j (specialLocalData j).centralPeriod j.twist
          (mainTwist_admissible j)) 4 (centralPeriodHomologyEquiv j 4 a) at h
  refine (congrArg (surfaceH4Equiv j (specialLocalData j).centralPeriod) h).trans ?_
  have hc := centralRealCover_h4_coordinates j a
  rw [centralRealCover, singularHomologyMap_comp, LinearMap.comp_apply] at hc
  exact hc

/-- The original boundary map has this same signed coefficient on its
literal Wang fibre summand. -/
theorem boundaryFilling_fibre_h4_coordinates (j : Kind)
    (a : SingularHomology RealTorus₄ 4) :
    surfaceH4Equiv j (specialLocalData j).centralPeriod
        (ellipticPieceRetractionHomologyEquiv j 4
          (boundaryFillingHomologyMap (some j) 4
            (MappingTorusHomology.fibreHomologyMap (monodromy (some j)) 4 a))) =
      (j.order : ℤ) * γ j.twist * realTorusH4Equiv a := by
  have h := LinearMap.congr_fun (boundaryFillingHomologyMap_fibre (some j) 4) a
  change boundaryFillingHomologyMap (some j) 4
    (MappingTorusHomology.fibreHomologyMap (monodromy (some j)) 4 a) =
      singularHomologyMap (fibreToFilling (some j)) 4 a at h
  exact (congrArg
    (fun b => surfaceH4Equiv j (specialLocalData j).centralPeriod
      (ellipticPieceRetractionHomologyEquiv j 4 b)) h).trans
    (fibreToFilling_h4_coordinates j a)

/-- In the original ordered four-period marking the order-three coefficient is positive three. -/
theorem fibreToFilling_three_h4_coordinates (a : SingularHomology RealTorus₄ 4) :
    surfaceH4Equiv .three (specialLocalData .three).centralPeriod
        (ellipticPieceRetractionHomologyEquiv .three 4
          (singularHomologyMap (fibreToFilling (some Kind.three)) 4 a)) =
      3 * realTorusH4Equiv a := by
  simpa [Kind.order, Kind.twist, γ, ε] using fibreToFilling_h4_coordinates .three a

/-- The negative primitive order-four twist gives negative four in that same source marking. -/
theorem fibreToFilling_four_h4_coordinates (a : SingularHomology RealTorus₄ 4) :
    surfaceH4Equiv .four (specialLocalData .four).centralPeriod
        (ellipticPieceRetractionHomologyEquiv .four 4
          (singularHomologyMap (fibreToFilling (some Kind.four)) 4 a)) =
      -4 * realTorusH4Equiv a := by
  simpa [Kind.order, Kind.twist, γ, ε'] using fibreToFilling_h4_coordinates .four a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticTopFibre
