import Wikipedia.HopfProblem.ConstantSheafSingularComparisonConcreteCoefficients
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLocalContractibility

/-!
# Sheaf--singular comparisons on the original geometric spaces

These degree-one and degree-two comparisons apply to the actual toric
normalization component `E₀`, the original Riemann sphere, and the glued
threefold.  Their compactness, Hausdorffness, and local contractibility
are proved properties of those original spaces.  In particular, the
threefold comparisons do not use a sphere-identification hypothesis.

The complex endpoints use the additive sheaf underlying the original
constant complex ring sheaf.  The integral endpoints have the original
integer-linear singular cohomology groups as their literal targets.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open CuspNormalization.SheafConstants

attribute [local instance] SpecialPeriods.Threefold.space_compact
  SpecialPeriods.Threefold.space_t2Space

/-! ## The normalization component `E₀` -/

/-- Arbitrary-coefficient constant-sheaf H¹ on the original `E₀`. -/
def normalizationConstantSheafH1Iso (A : AddCommGrpCat.{0}) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf
        (TopCat.of (ToricSpace.rayDivisor 0)) A) 1) ≅
      (singularCochainComplex (ToricSpace.rayDivisor 0) A).homology 1 :=
  constantSheafH1Iso (TopCat.of (ToricSpace.rayDivisor 0)) A
    LocalContractibility.normalization_locallyContractibleSpace

/-- Arbitrary-coefficient constant-sheaf H² on the original `E₀`. -/
def normalizationConstantSheafH2Iso (A : AddCommGrpCat.{0}) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf
        (TopCat.of (ToricSpace.rayDivisor 0)) A) 2) ≅
      (singularCochainComplex (ToricSpace.rayDivisor 0) A).homology 2 :=
  constantSheafH2Iso (TopCat.of (ToricSpace.rayDivisor 0)) A
    LocalContractibility.normalization_locallyContractibleSpace

/-- H¹ of the original constant complex sheaf on the actual normalization. -/
def normalizationComplexSheafH1Iso :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of (ToricSpace.rayDivisor 0))) 1) ≅
      (singularCochainComplex (ToricSpace.rayDivisor 0) (AddCommGrpCat.of ℂ)).homology 1 :=
  complexSheafH1Iso (TopCat.of (ToricSpace.rayDivisor 0))
    LocalContractibility.normalization_locallyContractibleSpace

/-- H² of the original constant complex sheaf on the actual normalization. -/
def normalizationComplexSheafH2Iso :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of (ToricSpace.rayDivisor 0))) 2) ≅
      (singularCochainComplex (ToricSpace.rayDivisor 0) (AddCommGrpCat.of ℂ)).homology 2 :=
  complexSheafH2Iso (TopCat.of (ToricSpace.rayDivisor 0))
    LocalContractibility.normalization_locallyContractibleSpace

/-- The original integral H¹ endpoint on the normalization component. -/
def normalizationIntegralSheafH1Equiv :
    CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of (ToricSpace.rayDivisor 0))
        (AddCommGrpCat.of ℤ)) 1 ≃+
      SingularCohomologyFree.SingularCohomology (ToricSpace.rayDivisor 0) 1 :=
  integralSheafH1Equiv (TopCat.of (ToricSpace.rayDivisor 0))
    LocalContractibility.normalization_locallyContractibleSpace

/-- The original integral H² endpoint on the normalization component. -/
def normalizationIntegralSheafH2Equiv :
    CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of (ToricSpace.rayDivisor 0))
        (AddCommGrpCat.of ℤ)) 2 ≃+
      SingularCohomologyFree.SingularCohomology (ToricSpace.rayDivisor 0) 2 :=
  integralSheafH2Equiv (TopCat.of (ToricSpace.rayDivisor 0))
    LocalContractibility.normalization_locallyContractibleSpace

/-! ## The original Riemann sphere -/

/-- Arbitrary-coefficient constant-sheaf H¹ on the actual Riemann sphere. -/
def sphereConstantSheafH1Iso (A : AddCommGrpCat.{0}) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of RiemannSphere) A) 1) ≅
      (singularCochainComplex RiemannSphere A).homology 1 :=
  constantSheafH1Iso (TopCat.of RiemannSphere) A
    LocalContractibility.sphere_locallyContractibleSpace

/-- Arbitrary-coefficient constant-sheaf H² on the actual Riemann sphere. -/
def sphereConstantSheafH2Iso (A : AddCommGrpCat.{0}) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of RiemannSphere) A) 2) ≅
      (singularCochainComplex RiemannSphere A).homology 2 :=
  constantSheafH2Iso (TopCat.of RiemannSphere) A
    LocalContractibility.sphere_locallyContractibleSpace

/-- H¹ of the original constant complex sheaf on the sphere. -/
def sphereComplexSheafH1Iso :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of RiemannSphere)) 1) ≅
      (singularCochainComplex RiemannSphere (AddCommGrpCat.of ℂ)).homology 1 :=
  complexSheafH1Iso (TopCat.of RiemannSphere)
    LocalContractibility.sphere_locallyContractibleSpace

/-- H² of the original constant complex sheaf on the sphere. -/
def sphereComplexSheafH2Iso :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of RiemannSphere)) 2) ≅
      (singularCochainComplex RiemannSphere (AddCommGrpCat.of ℂ)).homology 2 :=
  complexSheafH2Iso (TopCat.of RiemannSphere)
    LocalContractibility.sphere_locallyContractibleSpace

/-- The original integral H¹ endpoint on the sphere. -/
def sphereIntegralSheafH1Equiv :
    CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of RiemannSphere)
        (AddCommGrpCat.of ℤ)) 1 ≃+
      SingularCohomologyFree.SingularCohomology RiemannSphere 1 :=
  integralSheafH1Equiv (TopCat.of RiemannSphere)
    LocalContractibility.sphere_locallyContractibleSpace

/-- The original integral H² endpoint on the sphere. -/
def sphereIntegralSheafH2Equiv :
    CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of RiemannSphere)
        (AddCommGrpCat.of ℤ)) 2 ≃+
      SingularCohomologyFree.SingularCohomology RiemannSphere 2 :=
  integralSheafH2Equiv (TopCat.of RiemannSphere)
    LocalContractibility.sphere_locallyContractibleSpace

/-! ## The actual glued threefold -/

/-- Arbitrary-coefficient constant-sheaf H¹ on the constructed threefold. -/
def threefoldConstantSheafH1Iso (A : AddCommGrpCat.{0}) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf
        (TopCat.of SpecialPeriods.Threefold.Space) A) 1) ≅
      (singularCochainComplex SpecialPeriods.Threefold.Space A).homology 1 :=
  constantSheafH1Iso (TopCat.of SpecialPeriods.Threefold.Space) A
    LocalContractibility.threefold_locallyContractibleSpace

/-- Arbitrary-coefficient constant-sheaf H² on the constructed threefold. -/
def threefoldConstantSheafH2Iso (A : AddCommGrpCat.{0}) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf
        (TopCat.of SpecialPeriods.Threefold.Space) A) 2) ≅
      (singularCochainComplex SpecialPeriods.Threefold.Space A).homology 2 :=
  constantSheafH2Iso (TopCat.of SpecialPeriods.Threefold.Space) A
    LocalContractibility.threefold_locallyContractibleSpace

/-- H¹ of the original constant complex sheaf on the constructed threefold. -/
def threefoldComplexSheafH1Iso :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of SpecialPeriods.Threefold.Space)) 1) ≅
      (singularCochainComplex SpecialPeriods.Threefold.Space (AddCommGrpCat.of ℂ)).homology 1 :=
  complexSheafH1Iso (TopCat.of SpecialPeriods.Threefold.Space)
    LocalContractibility.threefold_locallyContractibleSpace

/-- H² of the original constant complex sheaf on the constructed threefold. -/
def threefoldComplexSheafH2Iso :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of SpecialPeriods.Threefold.Space)) 2) ≅
      (singularCochainComplex SpecialPeriods.Threefold.Space (AddCommGrpCat.of ℂ)).homology 2 :=
  complexSheafH2Iso (TopCat.of SpecialPeriods.Threefold.Space)
    LocalContractibility.threefold_locallyContractibleSpace

/-- The original integral H¹ endpoint on the constructed threefold. -/
def threefoldIntegralSheafH1Equiv :
    CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of SpecialPeriods.Threefold.Space)
        (AddCommGrpCat.of ℤ)) 1 ≃+
      SingularCohomologyFree.SingularCohomology SpecialPeriods.Threefold.Space 1 :=
  integralSheafH1Equiv (TopCat.of SpecialPeriods.Threefold.Space)
    LocalContractibility.threefold_locallyContractibleSpace

/-- The original integral H² endpoint on the constructed threefold. -/
def threefoldIntegralSheafH2Equiv :
    CategoryTheory.Sheaf.H.{0}
      (ConstantSheafFirstCohomology.Constant.sheaf (TopCat.of SpecialPeriods.Threefold.Space)
        (AddCommGrpCat.of ℤ)) 2 ≃+
      SingularCohomologyFree.SingularCohomology SpecialPeriods.Threefold.Space 2 :=
  integralSheafH2Equiv (TopCat.of SpecialPeriods.Threefold.Space)
    LocalContractibility.threefold_locallyContractibleSpace

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
