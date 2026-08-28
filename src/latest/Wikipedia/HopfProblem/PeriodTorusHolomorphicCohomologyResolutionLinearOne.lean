import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionForget
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionNaturality

/-!
# Linear degree-one comparison for an actual smooth resolution

This helper combines the genuine Ext/resolution comparison with an
isomorphism of actual global-section complexes. Compatibility of the
original sheaf scalar maps with that isomorphism proves linearity.
No scalar structure is assigned through a dimension calculation.
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

/-- The actual Ext comparison followed by the given genuine global-complex comparison. -/
def h1AddEquiv : CategoryTheory.Sheaf.H.{0} R.F 1 ≃+ S.homology :=
  (R.h1Iso ≪≫ ShortComplex.homologyMapIso e ≪≫
    S.mapHomologyIso linearForget).addCommGroupIsoToAddEquiv

variable (ρ : ℂ →+* End R.F) (γ : ℂ → R.Hom R)
  (haug : ∀ c, (γ c).augmentation = (ρ c).asHom)
  (hscalar : ∀ c, (γ c).globalMap ≫ e.hom = e.hom ≫ forgottenScalarMap S c)

include γ haug hscalar in
/-- Actual scalar naturality, retaining the original Ext action. -/
theorem h1AddEquiv_smul (c : ℂ) (a : CategoryTheory.Sheaf.H.{0} R.F 1) :
    letI := cohomologyModule R.F ρ 1
    h1AddEquiv R S e (c • a) = c • h1AddEquiv R S e a := by
  let := cohomologyModule R.F ρ 1
  have hn := ConcreteCategory.congr_hom ((γ c).h1Iso_naturality) a
  rw [haug c] at hn
  have he := congrArg
    (fun φ : R.globalComplex ⟶ S.map linearForget => ShortComplex.homologyMap φ)
    (hscalar c)
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at he
  have he' := ConcreteCategory.congr_hom he (R.h1Iso.hom a)
  change homologyForgetAddEquiv S
      (ShortComplex.homologyMap e.hom (R.h1Iso.hom (c • a))) =
    c • homologyForgetAddEquiv S (ShortComplex.homologyMap e.hom (R.h1Iso.hom a))
  exact (congrArg (homologyForgetAddEquiv S)
    ((congrArg (ShortComplex.homologyMap e.hom) hn).trans he')).trans
      (homologyForget_scalar S c _)

/-- The genuine degree-one comparison is linear for the actual sheaf-induced scalars. -/
def h1LinearEquiv :
    letI := cohomologyModule R.F ρ 1
    CategoryTheory.Sheaf.H.{0} R.F 1 ≃ₗ[ℂ] S.homology := by
  letI := cohomologyModule R.F ρ 1
  exact
    { __ := h1AddEquiv R S e
      map_smul' := h1AddEquiv_smul R S e ρ γ haug hscalar }

@[simp] theorem h1LinearEquiv_apply (a : CategoryTheory.Sheaf.H.{0} R.F 1) :
    letI := cohomologyModule R.F ρ 1
    h1LinearEquiv R S e ρ γ haug hscalar a = h1AddEquiv R S e a := rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.ResolutionLinear
