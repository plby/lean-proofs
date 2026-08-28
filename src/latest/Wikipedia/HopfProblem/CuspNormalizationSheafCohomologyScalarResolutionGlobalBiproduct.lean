import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionBiproduct
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsBiproduct

/-!
# Actual finite-sum scalar maps on global sections
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafCohomologyResolution SheafCohomologyGlobalSections

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {X : TopCat.{0}} {ι : Type} [Finite ι]
  (A : ι → TopCat.Sheaf AddCommGrpCat.{0} X)
  (ρ : ∀ i, ℂ →+* End (A i)) [∀ i, Module ℂ (Sections (A i))]
  (hρ : ∀ i (c : ℂ) (s : Sections (A i)),
    (globalSectionsFunctor X).map (ρ i c) s = c • s)

include hρ

/-- The actual biproduct scalar endomorphism acts by the original componentwise module. -/
theorem finiteGlobalScalar_apply (c : ℂ) (s : Sections (⨁ A)) :
    letI := finiteSectionsModule A
    (globalSectionsFunctor X).map (biproductScalarEnd A ρ c) s = c • s := by
  let := finiteSectionsModule A
  apply (finiteSectionsLinearEquiv A).injective
  funext i
  have hm : (globalSectionsFunctor X).map (biproductScalarEnd A ρ c) ≫
      (globalSectionsFunctor X).map (biproduct.π A i) =
    (globalSectionsFunctor X).map (biproduct.π A i) ≫
      (globalSectionsFunctor X).map (ρ i c) :=
    Eq.trans ((globalSectionsFunctor X).map_comp _ _).symm
      (Eq.trans (congrArg (globalSectionsFunctor X).map (biproductScalarEnd_π A ρ c i))
        ((globalSectionsFunctor X).map_comp _ _))
  exact Eq.trans (finiteSectionsEquiv_apply A
    ((globalSectionsFunctor X).map (biproductScalarEnd A ρ c) s) i)
    (Eq.trans (ConcreteCategory.congr_hom hm s)
      (Eq.trans (hρ i c ((globalSectionsFunctor X).map (biproduct.π A i) s))
        (Eq.trans (finiteSections_smul_component A c s i).symm
          (finiteSectionsEquiv_apply A (c • s) i).symm)))

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
