import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionExtOne
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardExt

/-!
# Composition and comparison of the original degree-one Ext maps

The maps are the original exact-functor Ext maps preceded by actual
endpoint morphisms. Their composition and a natural transformation of
the exact functors have the expected genuine endpoint formulas, by
the proved functoriality on actual degree-one extension classes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.ExtOne

open CuspNormalization.SheafCohomologyFinitePushforward

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w} E]

/-- Native exact comparisons compose through the actual composite endpoint. -/
theorem comparison_comp
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (S : D ⥤ E) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    {V F : C} {A : D} {B : E} (η : A ⟶ R.obj V) (ν : B ⟶ S.obj A)
    (α : Ext.{w} V F 1) :
    ExtComparison.comparison S ν (R.obj F) 1 (ExtComparison.comparison R η F 1 α) =
      ExtComparison.comparison (R ⋙ S) (ν ≫ S.map η) F 1 α := by
  change (Ext.mk₀ ν).comp
    (((Ext.mk₀ η).comp (α.mapExactFunctor R) (zero_add 1)).mapExactFunctor S)
      (zero_add 1) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    mapExactFunctor_comp_functor]
  exact Ext.mk₀_comp_mk₀_assoc ν (S.map η) (α.mapExactFunctor (R ⋙ S))

/-- A genuine natural transformation compares the actual maps after
the corresponding coefficient endpoint, retaining the original source endpoint. -/
theorem comparison_natTrans
    (R S : C ⥤ D)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (ρ : R ⟶ S) {V F : C} {A : D} (η : A ⟶ R.obj V) (α : Ext.{w} V F 1) :
    (ExtComparison.comparison R η F 1 α).comp (Ext.mk₀ (ρ.app F)) (add_zero 1) =
      ExtComparison.comparison S (η ≫ ρ.app V) F 1 α := by
  change ((Ext.mk₀ η).comp (α.mapExactFunctor R) (zero_add 1)).comp
    (Ext.mk₀ (ρ.app F)) (add_zero 1) = _
  rw [Ext.comp_assoc_of_third_deg_zero]
  rw [mapExactFunctor_naturality R S ρ α]
  exact Ext.mk₀_comp_mk₀_assoc η (ρ.app V) (α.mapExactFunctor S)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.ExtOne
