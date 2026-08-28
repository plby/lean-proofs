import Wikipedia.HopfProblem.ThreefoldHomologyFifthBoundary
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticTopFibre

/-!
# The actual integral cap equations in fifth homology

The native fourth fibre maps into the elliptic caps have signed
coefficients `3` and `-4`.  The native cusp fibre map is an actual
isomorphism; the cap image of the geometric cusp reference class
therefore defines an integer, whose value is not assumed or computed.
Applying these genuine maps to the Wang decompositions gives the three
integral equations used below.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree

open SingularMayerVietoris MappingTorusHomology ThreefoldOverlapMappingTorus
open PeriodTorusHigherHomology ThreefoldHomologyCuspFibre
open TrianglePeriodFamily TrianglePeriodFamily.Boundary.EllipticCapProduct
open TrianglePeriodFamily.Boundary.EllipticTopFibre
open Elliptic Elliptic.HigherHomology SpecialPeriods.EllipticFilling
open Finiteness FourthWang

/-- The actual cap coefficient of the geometric cusp reference class.
No value, in particular no vanishing, is assigned to this integer. -/
def cuspResidualCoefficient : ℤ :=
  realTorusH4Equiv
    (cuspFibreFourEquiv.symm (boundaryFillingHomologyMap none 4 CuspBoundaryGammaZero.nativeClass))

/-- The literal cusp cap map determines the fibre coefficient of a decomposed fifth class. -/
theorem cuspFibre_coordinate_of_decomposition (a : SingularHomology Space 5)
    (b : SingularHomology RealTorus₄ 4)
    (hb : fibreHomologyMap (monodromy none) 4 b =
      nativeFifthBoundary a none - fifthWangCoordinate a • fifthReferenceBoundary none) :
    realTorusH4Equiv b = -(fifthWangCoordinate a * cuspResidualCoefficient) := by
  have h := congrArg (boundaryFillingHomologyMap none 4) hb
  rw [cuspCap_four_fibre, map_sub, map_zsmul, nativeFifthBoundary_cap_zero,
    fifthReferenceBoundary_cusp, zero_sub] at h
  have hc := congrArg (fun x => realTorusH4Equiv (cuspFibreFourEquiv.symm x)) h
  simpa only [LinearEquiv.symm_apply_apply, map_neg, map_zsmul, smul_eq_mul,
    cuspResidualCoefficient] using hc

/-- The original signed finite-cover map gives the elliptic cap equation. -/
theorem ellipticFibre_coordinate_of_decomposition (j : Kind)
    (a : SingularHomology Space 5) (b : SingularHomology RealTorus₄ 4)
    (hb : fibreHomologyMap (monodromy (some j)) 4 b =
      nativeFifthBoundary a (some j) - fifthWangCoordinate a • fifthReferenceBoundary (some j)) :
    (j.order : ℤ) * γ j.twist * realTorusH4Equiv b = fifthWangCoordinate a := by
  let c : SingularHomology (Boundary (some j)) 4 →ₗ[ℤ] ℤ :=
    (surfaceH4Equiv j (specialLocalData j).centralPeriod).toLinearMap.comp
      ((ellipticPieceRetractionHomologyEquiv j 4).toLinearMap.comp
        (boundaryFillingHomologyMap (some j) 4))
  have hunit : c (unitCapSectionClass j) = 1 := unitCapSectionClass_filling j
  have href : c (fifthReferenceBoundary (some j)) = -1 :=
    (map_neg c (unitCapSectionClass j)).trans (congrArg Neg.neg hunit)
  have hzero : c (nativeFifthBoundary a (some j)) = 0 := by
    change surfaceH4Equiv j (specialLocalData j).centralPeriod
      (ellipticPieceRetractionHomologyEquiv j 4
        (boundaryFillingHomologyMap (some j) 4 (nativeFifthBoundary a (some j)))) = 0
    rw [nativeFifthBoundary_cap_zero, map_zero, map_zero]
  have hfibre : c (fibreHomologyMap (monodromy (some j)) 4 b) =
      (j.order : ℤ) * γ j.twist * realTorusH4Equiv b :=
    boundaryFilling_fibre_h4_coordinates j b
  have h := congrArg c hb
  rw [hfibre, map_sub, map_zsmul, hzero, href] at h
  simpa using h

/-- The actual order-three cap coefficient is positive three. -/
theorem threeFibre_coordinate_of_decomposition (a : SingularHomology Space 5)
    (b : SingularHomology RealTorus₄ 4)
    (hb : fibreHomologyMap (monodromy (some Kind.three)) 4 b =
      nativeFifthBoundary a (some .three) -
        fifthWangCoordinate a • fifthReferenceBoundary (some .three)) :
    3 * realTorusH4Equiv b = fifthWangCoordinate a := by
  simpa [Kind.order, Kind.twist, γ, ε] using
    ellipticFibre_coordinate_of_decomposition .three a b hb

/-- The actual negative primitive order-four twist gives coefficient negative four. -/
theorem fourFibre_coordinate_of_decomposition (a : SingularHomology Space 5)
    (b : SingularHomology RealTorus₄ 4)
    (hb : fibreHomologyMap (monodromy (some Kind.four)) 4 b =
      nativeFifthBoundary a (some .four) -
        fifthWangCoordinate a • fifthReferenceBoundary (some .four)) :
    -4 * realTorusH4Equiv b = fifthWangCoordinate a := by
  simpa [Kind.order, Kind.twist, γ, ε'] using
    ellipticFibre_coordinate_of_decomposition .four a b hb

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FifthDegree
