import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionNaturality

/-!
# Complex-linearity of genuine resolution comparisons

Naturality under actual scalar morphisms of an augmented resolution
makes its Ext/global-complex comparisons linear. Positive degrees keep
exactly the term-acyclicity hypotheses required by the generic comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafCohomology SheafCohomologyResolution

variable {X : TopCat.{0}}
  (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))
  (ρ : ℂ →+* End R.F) (γ : ℂ → R.Hom R)
  (haug : ∀ c, (γ c).augmentation = (ρ c).asHom)

section Zero

variable [Module ℂ ↥(kernel R.globalComplex.f)]
  (hscalar : ∀ c (a : ↥(kernel R.globalComplex.f)), (γ c).globalKernelMap a = c • a)

/-- The actual degree-zero comparison is linear for the original scalar action. -/
def h0ResolutionLinearEquiv :
    letI := cohomologyModule R.F ρ 0
    CategoryTheory.Sheaf.H.{0} R.F 0 ≃ₗ[ℂ] ↥(kernel R.globalComplex.f) := by
  letI := cohomologyModule R.F ρ 0
  refine { __ := R.h0Iso.addCommGroupIsoToAddEquiv, map_smul' := ?_ }
  intro c a
  have h := ConcreteCategory.congr_hom ((γ c).h0Iso_naturality) a
  rw [haug c] at h
  exact Eq.trans h (hscalar c (R.h0Iso.hom a))

@[simp] theorem h0ResolutionLinearEquiv_apply (a : CategoryTheory.Sheaf.H.{0} R.F 0) :
    letI := cohomologyModule R.F ρ 0
    h0ResolutionLinearEquiv R ρ γ haug hscalar a = R.h0Iso.hom a := rfl

end Zero

section One

variable [Module ℂ R.globalComplex.homology]
  (hscalar : ∀ c (a : R.globalComplex.homology),
    ShortComplex.homologyMap (γ c).globalMap a = c • a)
  [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]

/-- The actual degree-one comparison is linear once the first resolution term is H¹-acyclic. -/
def h1ResolutionLinearEquiv :
    letI := cohomologyModule R.F ρ 1
    CategoryTheory.Sheaf.H.{0} R.F 1 ≃ₗ[ℂ] R.globalComplex.homology := by
  letI := cohomologyModule R.F ρ 1
  refine { __ := R.h1Iso.addCommGroupIsoToAddEquiv, map_smul' := ?_ }
  intro c a
  have h := ConcreteCategory.congr_hom ((γ c).h1Iso_naturality) a
  rw [haug c] at h
  exact Eq.trans h (hscalar c (R.h1Iso.hom a))

@[simp] theorem h1ResolutionLinearEquiv_apply (a : CategoryTheory.Sheaf.H.{0} R.F 1) :
    letI := cohomologyModule R.F ρ 1
    h1ResolutionLinearEquiv R ρ γ haug hscalar a = R.h1Iso.hom a := rfl

end One

section Two

variable [Module ℂ ↥(cokernel R.globalComplex.g)]
  (hscalar : ∀ c (a : ↥(cokernel R.globalComplex.g)), (γ c).globalCokernelMap a = c • a)
  [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
  [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)]
  [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)]

/-- The actual degree-two comparison is linear under its genuine term-acyclicity inputs. -/
def h2ResolutionLinearEquiv :
    letI := cohomologyModule R.F ρ 2
    CategoryTheory.Sheaf.H.{0} R.F 2 ≃ₗ[ℂ] ↥(cokernel R.globalComplex.g) := by
  letI := cohomologyModule R.F ρ 2
  refine { __ := R.h2Iso.addCommGroupIsoToAddEquiv, map_smul' := ?_ }
  intro c a
  have h := ConcreteCategory.congr_hom ((γ c).h2Iso_naturality) a
  rw [haug c] at h
  exact Eq.trans h (hscalar c (R.h2Iso.hom a))

@[simp] theorem h2ResolutionLinearEquiv_apply (a : CategoryTheory.Sheaf.H.{0} R.F 2) :
    letI := cohomologyModule R.F ρ 2
    h2ResolutionLinearEquiv R ρ γ haug hscalar a = R.h2Iso.hom a := rfl

end Two

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
