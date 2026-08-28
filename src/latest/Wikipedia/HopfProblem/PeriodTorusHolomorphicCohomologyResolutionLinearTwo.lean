import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyResolutionLinearCokernel

/-!
# Linear degree-two comparison for an actual smooth resolution

The actual double connecting map identifies sheaf cohomology with the
last global cokernel. A genuine comparison of global complexes and
scalar naturality retain the original sheaf-induced complex action.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.ResolutionLinear

open CuspNormalization.SheafCohomology
open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyScalarResolution

variable {X : TopCat.{0}}
  (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))
  (S : ShortComplex (ModuleCat.{0} ℂ))
  (e : R.globalComplex ≅ S.map linearForget)

variable [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
  [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)]
  [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)]

/-- The actual degree-two Ext comparison followed by the genuine global-complex comparison. -/
def h2AddEquiv : CategoryTheory.Sheaf.H.{0} R.F 2 ≃+ ↥(cokernel S.g) :=
  (R.h2Iso ≪≫ cokernelComplexIso e ≪≫
    (PreservesCokernel.iso linearForget S.g).symm).addCommGroupIsoToAddEquiv

variable (ρ : ℂ →+* End R.F) (γ : ℂ → R.Hom R)
  (haug : ∀ c, (γ c).augmentation = (ρ c).asHom)
  (hscalar : ∀ c, (γ c).globalMap ≫ e.hom = e.hom ≫ forgottenScalarMap S c)

include γ haug hscalar in
/-- The actual scalar sheaf maps induce the ordinary scalar action on the last cokernel. -/
theorem h2AddEquiv_smul (c : ℂ) (a : CategoryTheory.Sheaf.H.{0} R.F 2) :
    letI := cohomologyModule R.F ρ 2
    h2AddEquiv R S e (c • a) = c • h2AddEquiv R S e a := by
  let := cohomologyModule R.F ρ 2
  have hn := ConcreteCategory.congr_hom ((γ c).h2Iso_naturality) a
  rw [haug c] at hn
  have he := ConcreteCategory.congr_hom
    (cokernelComplexIso_naturality e (γ c).globalMap (forgottenScalarMap S c)
      (hscalar c)) (R.h2Iso.hom a)
  change cokernelForgetAddEquiv S
      ((cokernelComplexIso e).hom (R.h2Iso.hom (c • a))) =
    c • cokernelForgetAddEquiv S ((cokernelComplexIso e).hom (R.h2Iso.hom a))
  exact (congrArg (cokernelForgetAddEquiv S)
    ((congrArg (cokernelComplexIso e).hom hn).trans he)).trans
      (cokernelForget_scalar S c _)

/-- Complex linearity comes from actual scalar naturality before any dimension calculation. -/
def h2LinearEquiv :
    letI := cohomologyModule R.F ρ 2
    CategoryTheory.Sheaf.H.{0} R.F 2 ≃ₗ[ℂ] ↥(cokernel S.g) := by
  letI := cohomologyModule R.F ρ 2
  exact
    { __ := h2AddEquiv R S e
      map_smul' := h2AddEquiv_smul R S e ρ γ haug hscalar }

@[simp] theorem h2LinearEquiv_apply (a : CategoryTheory.Sheaf.H.{0} R.F 2) :
    letI := cohomologyModule R.F ρ 2
    h2LinearEquiv R S e ρ γ haug hscalar a = h2AddEquiv R S e a := rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.ResolutionLinear
