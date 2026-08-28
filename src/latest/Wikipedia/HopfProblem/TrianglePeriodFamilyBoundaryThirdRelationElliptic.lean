import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationCover
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationUntwisted
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationShearCoordinates
import Wikipedia.HopfProblem.ThreefoldHomologyThirdClasses

/-!
# The complete original elliptic contributions in degree three

Each reference cap-kernel class is represented by the actual finite
covering product.  The full native regular map splits into a genuine
negation-invariant horizontal class and the computed positive four or
negative three original fibre classes.  No regular-family splitting
coordinate is assigned to an attaching map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open Elliptic SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus EllipticCapProduct EllipticCapKernelWang
open EllipticGaugeLinearization Homology
open SpecialPeriods.Threefold.Homology.ThirdDegree

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The literal two finite-cover fibre inputs of the reference classes. -/
def referenceCoverInput : Kind → SingularHomology RealTorus₄ 2
  | .three => 4 • splitFibreClassTwo .three + 2 • splitCircleClassTwo .three
  | .four => 3 • splitFibreClassTwo .four - splitCircleClassTwo .four

/-- The full native cap-kernel classes, not just their Wang images, have these representatives. -/
theorem referenceClasses_elliptic_cover (j : Kind) :
    (referenceClasses (some j)).val =
      singularHomologyMap (nativeProductCover j) 3
        (positiveCircleCross RealTorus₄ 2 (referenceCoverInput j)) := by
  cases j
  · change ((boundaryCapKernelEquiv .three 2).symm _).val = _
    rw [boundaryCapKernelEquiv_symm_val]
    simpa only [referenceCoverInput, ofNat_zsmul] using! capCircle_three_reference
  · change ((boundaryCapKernelEquiv .four 2).symm _).val = _
    rw [boundaryCapKernelEquiv_symm_val]
    simpa only [referenceCoverInput, ofNat_zsmul] using! capCircle_four_reference

/-- The genuine original regular image of the reference class is the full covered map. -/
theorem referenceClasses_elliptic_regular_cover (j : Kind) :
    boundaryRegularHomologyMap (some j) 3 (referenceClasses (some j)).val =
      singularHomologyMap (coveredRegularMap j 0) 3
        (positiveCircleCross RealTorus₄ 2 (referenceCoverInput j)) := by
  rw [referenceClasses_elliptic_cover, boundaryRegularHomologyMap_linear j 0 3]
  exact (LinearMap.congr_fun
    (singularHomologyMap_comp (nativeProductCover j) (linearRegularBoundaryMap j 0) 3)
    (positiveCircleCross RealTorus₄ 2 (referenceCoverInput j))).symm

/-- The unchanged horizontal representative in the original regular family. -/
def ellipticHorizontal (j : Kind) : SingularHomology (Dsp).Space 3 :=
  singularHomologyMap (untwistedRegularMap j 0) 3
    (positiveCircleCross RealTorus₄ 2 (referenceCoverInput j))

theorem ellipticHorizontal_negation (j : Kind) :
    singularHomologyMap (familyNegation Dsp) 3 (ellipticHorizontal j) =
      ellipticHorizontal j :=
  untwistedRegularMap_positiveCircleCross_negation j 0 (referenceCoverInput j)

/-- The actual positive original `γ,u,w` fibre included in the regular family. -/
def regularGammaUW : SingularHomology (Dsp).Space 3 :=
  singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 3 gammaUWClass

/-- The order-three original attachment contributes exactly four positive fibre classes. -/
theorem referenceClasses_three_regular :
    boundaryRegularHomologyMap (some .three) 3 (referenceClasses (some .three)).val =
      ellipticHorizontal .three + (4 : ℤ) • regularGammaUW := by
  rw [referenceClasses_elliptic_regular_cover, coveredRegularMap_positiveCircleCross]
  change ellipticHorizontal .three +
    singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 3
      (PeriodTorusHigherHomologyPontryagin.product RealTorus₄ 2
        (FlatTorus.singularH1Equiv.symm Kind.three.twist) (referenceCoverInput .three)) = _
  rw [referenceCoverInput, three_shear_correction, map_zsmul]
  rfl

/-- The order-four original attachment retains the opposite twist sign
and contributes minus three. -/
theorem referenceClasses_four_regular :
    boundaryRegularHomologyMap (some .four) 3 (referenceClasses (some .four)).val =
      ellipticHorizontal .four + (-3 : ℤ) • regularGammaUW := by
  rw [referenceClasses_elliptic_regular_cover, coveredRegularMap_positiveCircleCross]
  change ellipticHorizontal .four +
    singularHomologyMap (familyFibreInclusion Dsp normalizedSlitBaseLift) 3
      (PeriodTorusHigherHomologyPontryagin.product RealTorus₄ 2
        (FlatTorus.singularH1Equiv.symm Kind.four.twist) (referenceCoverInput .four)) = _
  rw [referenceCoverInput, four_shear_correction, map_zsmul]
  rfl

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
