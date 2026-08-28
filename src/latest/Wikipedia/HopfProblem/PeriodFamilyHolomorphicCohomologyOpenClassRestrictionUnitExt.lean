import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionUnitBasic

/-!
# The native all-degree Ext formula for the original restriction endpoint

The canonical open comparison of a globally restricted class is the
original exact-functor image preceded by the actual integer endpoint.
This is an equality of maps on Mathlib's genuine Ext classes, not a
new definition of the cohomology comparison.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction

open HolomorphicSheafCohomology
open CuspNormalization.SheafCohomologyFinitePushforward
open PeriodFamilyHigherDirectImage

private theorem exactComparison_precompose
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [HasExt.{0} C] [HasExt.{0} D] {V' V : C} {A : D}
    (η : A ⟶ R.obj V') (g : V' ⟶ V) (F : C) (q : ℕ) (a : Ext.{0} V F q) :
    ExtComparison.comparison R η F q ((Ext.mk₀ g).comp a (zero_add q)) =
      (Ext.mk₀ (η ≫ R.map g)).comp (a.mapExactFunctor R) (zero_add q) := by
  change (Ext.mk₀ η).comp
    (((Ext.mk₀ g).comp a (zero_add q)).mapExactFunctor R) (zero_add q) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact Ext.mk₀_comp_mk₀_assoc η (R.map g) (a.mapExactFunctor R)

variable {X : TopCat.{0}} (U : Opens X)

/-- The actual all-degree open comparison of a globally restricted
class is its native exact-functor image with the actual integer endpoint. -/
theorem cohomologyEquiv_restrictionMap (F : AbelianSheaf X) (q : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} F q) :
    OpenRestriction.cohomologyEquiv U F q (GlobalRestriction.restrictionMap F U q a) =
      (Ext.mk₀ (integerRestrictionUnit U)).comp
        (@Ext.mapExactFunctor (AbelianSheaf X) _ _ (AbelianSheaf (TopCat.of U)) _ _
          (OpenRestriction.restriction U) (OpenRestriction.restriction_additive U)
          (OpenRestriction.restriction_preservesFiniteLimits U)
          (OpenRestriction.restriction_preservesFiniteColimits U)
          (abelianSheaf_hasExt X) (abelianSheaf_hasExt (TopCat.of U))
          (integerSheaf X) F q a) (zero_add q) := by
  exact @exactComparison_precompose (AbelianSheaf X) (AbelianSheaf (TopCat.of U)) _ _ _ _
    (OpenRestriction.restriction U) (OpenRestriction.restriction_additive U)
    (OpenRestriction.restriction_preservesFiniteLimits U)
    (OpenRestriction.restriction_preservesFiniteColimits U)
    (abelianSheaf_hasExt X) (abelianSheaf_hasExt (TopCat.of U))
    (OpenRestriction.freeOpen U) (integerSheaf X) (integerSheaf (TopCat.of U))
    (OpenRestriction.representingUnit U) (GlobalRestriction.globalUnit U) F q a

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction
