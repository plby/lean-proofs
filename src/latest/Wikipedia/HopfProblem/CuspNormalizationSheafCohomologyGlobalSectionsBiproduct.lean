import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections
import Wikipedia.HopfProblem.CuspNormalizationSheafBiproduct
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Data.Complex.Basic

/-!
# Literal global sections of finite sums

The global-section comparison is the tuple of the actual sheaf
biproduct projections. Its complex module is the unique pointwise
one on these actual component sections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

open SheafCohomologyResolution

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {X : TopCat.{0}} {ι : Type} [Finite ι]

/-- Sections on the actual top open set, with their existing additive group. -/
abbrev Sections (F : TopCat.Sheaf AddCommGrpCat.{0} X) : Type :=
  (globalSectionsFunctor X).obj F

variable (A : ι → TopCat.Sheaf AddCommGrpCat.{0} X)

/-- The actual section functor's finite-biproduct comparison. -/
def finiteSectionsIso : (globalSectionsFunctor X).obj (⨁ A) ≅
    AddCommGrpCat.of (∀ i, Sections (A i)) :=
  ((globalSectionsFunctor X).mapBiproduct A) ≪≫
    AddCommGrpCat.biproductIsoPi ((globalSectionsFunctor X).obj ∘ A)

/-- The actual global-section comparison as an additive equivalence. -/
def finiteSectionsEquiv : Sections (⨁ A) ≃+ (∀ i, Sections (A i)) :=
  (finiteSectionsIso A).addCommGroupIsoToAddEquiv

@[reassoc] theorem finiteSectionsIso_hom_comp_eval (i : ι) :
    (finiteSectionsIso A).hom ≫
        AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun j => Sections (A j)) i) =
      (globalSectionsFunctor X).map (biproduct.π A i) := by
  change (((globalSectionsFunctor X).mapBiproduct A).hom ≫
      (AddCommGrpCat.biproductIsoPi ((globalSectionsFunctor X).obj ∘ A)).hom) ≫
        AddCommGrpCat.ofHom
          (Pi.evalAddMonoidHom (fun j => (globalSectionsFunctor X).obj (A j)) i) = _
  rw [Category.assoc, SheafBiproduct.biproductIsoPi_hom_comp_eval, Functor.mapBiproduct_hom]
  exact biproduct.lift_π (f := (globalSectionsFunctor X).obj ∘ A)
    (fun j => (globalSectionsFunctor X).map (biproduct.π A j)) i

/-- Each coordinate is the actual global section of the corresponding
categorical sheaf projection. -/
@[simp] theorem finiteSectionsEquiv_apply (s : Sections (⨁ A)) (i : ι) :
    finiteSectionsEquiv A s i = (globalSectionsFunctor X).map (biproduct.π A i) s :=
  ConcreteCategory.congr_hom (finiteSectionsIso_hom_comp_eval A i) s

variable [∀ i, Module ℂ (Sections (A i))]

/-- The canonical pointwise module on the actual finite-sum sections. -/
@[instance_reducible] def finiteSectionsModule : Module ℂ (Sections (⨁ A)) :=
  (finiteSectionsEquiv A).module ℂ

/-- The comparison of actual sections is complex linear for their
componentwise complex module. -/
def finiteSectionsLinearEquiv :
    letI := finiteSectionsModule A
    Sections (⨁ A) ≃ₗ[ℂ] (∀ i, Sections (A i)) := by
  letI := finiteSectionsModule A
  exact (finiteSectionsEquiv A).linearEquiv ℂ

/-- This module acts by the original scalar multiplication on every
actual sheaf-projection section. -/
theorem finiteSections_smul_component (c : ℂ) (s : Sections (⨁ A)) (i : ι) :
    letI := finiteSectionsModule A
    (globalSectionsFunctor X).map (biproduct.π A i) (c • s) =
      c • (globalSectionsFunctor X).map (biproduct.π A i) s := by
  let := finiteSectionsModule A
  rw [← finiteSectionsEquiv_apply, ← finiteSectionsEquiv_apply]
  exact congrFun ((finiteSectionsLinearEquiv A).map_smul c s) i

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
