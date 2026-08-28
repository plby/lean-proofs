import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageGlobalUnit
import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageFibreEvaluation

/-!
# Original global classes and their actual neighborhood fibre restrictions

The genuine Ext restriction from global cohomology is natural in both
the coefficient sheaf and the open set. Its fibre evaluation agrees
with the original global finite-closed-pushforward comparison. This
retains the actual extension class when it is used as a neighborhood
representative of a higher-direct-image stalk.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.GlobalRestriction

open HolomorphicSheafCohomology.OpenRestriction
open CuspNormalization.SheafCohomologyFinitePushforward
open SheafHigherDirectImage.Sections

private theorem comparison_precompose
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [HasExt.{0} C] [HasExt.{0} D] {Z : C} {A A' : D}
    (η : A ⟶ R.obj Z) (η' : A' ⟶ R.obj Z) (r : A' ⟶ A) (hr : r ≫ η = η')
    (G : C) (n : ℕ) (a : Ext.{0} Z G n) :
    (Ext.mk₀ r).comp (ExtComparison.comparison R η G n a) (zero_add n) =
      ExtComparison.comparison R η' G n a := by
  subst η'
  exact Ext.mk₀_comp_mk₀_assoc r η (a.mapExactFunctor R)

variable {X : TopCat.{0}}

/-- The canonical actual Ext restriction of a global class to an original open. -/
def restrictionMap (F : AbelianSheaf X) (U : Opens X) (n : ℕ) :
    CategoryTheory.Sheaf.H.{0} F n →+ ↥(CategoryTheory.Sheaf.H'.{0} F n U) :=
  (Ext.mk₀ (globalUnit U)).precomp F (zero_add n)

@[simp] theorem restrictionMap_apply (F : AbelianSheaf X) (U : Opens X) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} F n) :
    restrictionMap F U n a = (Ext.mk₀ (globalUnit U)).comp a (zero_add n) := rfl

/-- Global restriction uses precisely the original top-open Ext isomorphism. -/
theorem restrictionMap_top (F : AbelianSheaf X) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} F n) :
    restrictionMap F ⊤ n a = (topCohomologyEquiv X F n).symm a := by
  have h : globalUnit (⊤ : Opens X) = freeTopToInteger X := by
    have htop : (homOfLE le_top : (⊤ : Opens X) ⟶ ⊤) = 𝟙 _ := Subsingleton.elim _ _
    have hmap := (congrArg (freeOpenFunctor X).map htop).trans
      ((freeOpenFunctor X).map_id (⊤ : Opens X))
    exact (congrArg (fun u => u ≫ freeTopToInteger X) hmap).trans (Category.id_comp _)
  exact congrArg (fun u => (Ext.mk₀ u).comp a (zero_add n)) h

/-- Shrinking an open gives the original cohomology-presheaf restriction. -/
theorem restrictionMap_restrict (F : AbelianSheaf X) {U V : Opens X} (r : U ⟶ V)
    (n : ℕ) (a : CategoryTheory.Sheaf.H.{0} F n) :
    (CategoryTheory.Sheaf.cohomologyPresheaf F n).map r.op (restrictionMap F V n a) =
      restrictionMap F U n a := by
  exact (@Ext.mk₀_comp_mk₀_assoc (AbelianSheaf X) _ _ (abelianSheaf_hasExt X)
    (freeOpen U) (freeOpen V) (integerSheaf X) F
    ((freeOpenFunctor X).map r) (globalUnit V) n a).trans
    (congrArg (fun u => (Ext.mk₀ u).comp a (zero_add n)) (globalUnit_restrict r))

/-- Coefficient maps are the original native maps before and after restriction. -/
theorem restrictionMap_naturality {F G : AbelianSheaf X} (g : F ⟶ G)
    (U : Opens X) (n : ℕ) (a : CategoryTheory.Sheaf.H.{0} F n) :
    (((CategoryTheory.Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology X) n).map g).app (op U)) (restrictionMap F U n a) =
        restrictionMap G U n (CategoryTheory.Sheaf.H.map g n a) := by
  exact Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ (globalUnit U)) a (Ext.mk₀ g) (zero_add n)

variable {T : TopCat.{0}} [T2Space T] (i : T ⟶ X)
  (hi : IsClosedMap i) (hfinite : ∀ x : X, (i ⁻¹' {x}).Finite)
  (U : Opens X) (hU : ∀ t : T, i t ∈ U)

/-- Original global and neighborhood finite-pushforward maps agree after restriction. -/
theorem cohomologyForward_restriction (G : AbelianSheaf T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} G n) :
    restrictionMap ((pushforward i).obj G) U n (cohomologyForward i hi hfinite G n a) =
      FibreNeighborhood.cohomologyForward i hi hfinite U hU G n a := by
  exact @comparison_precompose
    (AbelianSheaf T) (AbelianSheaf X) _ _ _ _ (pushforward i) (pushforward_additive i)
    (pushforward_preservesFiniteLimitsAndColimits i hi hfinite).1
    (pushforward_preservesFiniteColimits i hi hfinite)
    (abelianSheaf_hasExt T) (abelianSheaf_hasExt X)
    (integerSheaf T) (integerSheaf X) (freeOpen U)
    (integerUnit i) (FibreNeighborhood.integerUnit i U hU) (globalUnit U)
    (globalUnit_integerUnit i U hU) G n a

/-- The actual neighborhood comparison of a restricted global class
is the original global finite-closed-pushforward comparison. -/
theorem cohomologyEquiv_restriction (G : AbelianSheaf T) (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} ((pushforward i).obj G) n) :
    FibreNeighborhood.cohomologyEquiv i hi hfinite U hU G n
        (restrictionMap ((pushforward i).obj G) U n a) =
      cohomologyEquiv i hi hfinite G n a := by
  obtain ⟨b, rfl⟩ := (cohomologyForward_bijective i hi hfinite G n).surjective a
  rw [cohomologyForward_restriction]
  exact (FibreNeighborhood.cohomologyEquiv i hi hfinite U hU G n).apply_symm_apply b |>.trans
    ((cohomologyEquiv i hi hfinite G n).apply_symm_apply b).symm

/-- Fibre evaluation preserves the original global coefficient restriction class. -/
theorem cohomologyEvaluation_restriction {F : AbelianSheaf X} {G : AbelianSheaf T}
    (κ : F ⟶ (pushforward i).obj G) (n : ℕ) (a : CategoryTheory.Sheaf.H.{0} F n) :
    FibreNeighborhood.cohomologyEvaluation i hi hfinite κ U hU n
        (restrictionMap F U n a) =
      cohomologyEquiv i hi hfinite G n (CategoryTheory.Sheaf.H.map κ n a) := by
  change FibreNeighborhood.cohomologyEquiv i hi hfinite U hU G n
    ((((CategoryTheory.Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology X) n).map κ).app (op U)) (restrictionMap F U n a)) = _
  rw [restrictionMap_naturality, cohomologyEquiv_restriction]

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.GlobalRestriction
