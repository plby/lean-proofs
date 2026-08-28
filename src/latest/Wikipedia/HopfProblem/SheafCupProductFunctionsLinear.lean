import Wikipedia.HopfProblem.SheafCupProductNativeLinearOriginal
import Wikipedia.HopfProblem.SheafCupProductFunctions

/-!
# Complex-bilinear products on the original function-sheaf cohomology

The holomorphic and reduced sheaves use their already constructed
pointwise scalar endomorphisms. The actual constant sheaf uses
multiplication by the sheafification unit's literal constants. The
underlying products are exactly the native cups already constructed.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SheafCupProduct

open CuspNormalization

/-- Actual constant-section multiplication on native constant-sheaf cohomology. -/
@[instance_reducible] def constantCohomologyModule (X : TopCat.{0}) (n : ℕ) :
    Module ℂ (CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) n) :=
  SheafCohomology.cohomologyModule (SheafConstants.complexAdditiveSheaf X)
    (constantScalarEnd X) n

/-- The actual constant-sheaf cup, complex-bilinear for its actual scalars. -/
def constantLinearCup (X : TopCat.{0}) :
    letI := constantCohomologyModule X 1
    letI := constantCohomologyModule X 2
    CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1 →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1 →ₗ[ℂ]
        CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 2 :=
  linearCupOfScalarEnd (constantCoefficients X) (constantScalarEnd X) rfl

@[simp] theorem constantLinearCup_apply (X : TopCat.{0})
    (a b : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1) :
    constantLinearCup X a b = constantCup X a b := rfl

section Holomorphic

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace B] (I : ModelWithCorners ℂ E B)
  (M : Type) [TopologicalSpace M] [ChartedSpace B M]

/-- Complex-bilinearity for the original pointwise holomorphic scalar action. -/
def holomorphicLinearCup :
    letI := SheafCohomology.holomorphicCohomologyModule I M 1
    letI := SheafCohomology.holomorphicCohomologyModule I M 2
    CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 1 →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 1 →ₗ[ℂ]
        CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 2 :=
  linearCupOfScalarEnd (holomorphicCoefficients I M)
    (SheafCohomology.holomorphicScalarEnd I M) (scalarEnd_holomorphicCoefficients I M)

@[simp] theorem holomorphicLinearCup_apply
    (a b : CategoryTheory.Sheaf.H.{0} (HolomorphicFunctionSheaf.additiveSheaf I M) 1) :
    holomorphicLinearCup I M a b = holomorphicCup I M a b := rfl

end Holomorphic

section Reduced

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace B] {M : Type} [TopologicalSpace M] [ChartedSpace B M]
  (I : ModelWithCorners ℂ E B) (S : Set M)

attribute [local instance] reducedHAddCommGroup

/-- The old pointwise reduced scalar endomorphisms induce this native module. -/
@[instance_reducible] def reducedFunctionCohomologyModule (n : ℕ) :
    Module ℂ (CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) n) :=
  SheafCohomology.cohomologyModule (SheafReduced.additiveSheaf I S)
    (SheafCohomologyScalarResolution.reducedScalarEnd I S) n

/-- The reduced holomorphic cup is bilinear for its original pointwise scalars. -/
def reducedLinearCup :
    letI := reducedFunctionCohomologyModule I S 1
    letI := reducedFunctionCohomologyModule I S 2
    CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) 1 →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) 1 →ₗ[ℂ]
        CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) 2 :=
  linearCupOfScalarEnd (reducedCoefficients I S)
    (SheafCohomologyScalarResolution.reducedScalarEnd I S) (scalarEnd_reducedCoefficients I S)

@[simp] theorem reducedLinearCup_apply
    (a b : CategoryTheory.Sheaf.H.{0} (SheafReduced.additiveSheaf I S) 1) :
    reducedLinearCup I S a b = reducedCup I S a b := rfl

end Reduced

end Wikipedia.HopfProblem.SheafCupProduct
