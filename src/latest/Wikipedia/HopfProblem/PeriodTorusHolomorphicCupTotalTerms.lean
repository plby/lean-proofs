import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalColumnsBasic

/-!
# The actual augmented total sheaf terms

The original holomorphic-function inclusion is followed by the genuine
smooth germ inclusion. All subsequent maps are the signed biproduct
maps of the actual Godement--Dolbeault diagram.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total.CompatibleOperators

open SheafCupProduct SheafSingularCupComparison

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {p : PeriodDomain} (D : CompatibleOperators p)

abbrev I0 := D.categoryData.zeroTerm
abbrev I1 := D.categoryData.oneTerm
abbrev I2 := D.categoryData.twoTerm
abbrev I3 := D.categoryData.threeTerm

abbrev d0 := D.categoryData.d0
abbrev d1 := D.categoryData.d1
abbrev d2 := D.categoryData.d2

/-- The original holomorphic inclusion followed by the original smooth germ map. -/
def augmentation : PeriodTorusHolomorphicCohomology.holomorphicSheaf p ⟶ D.I0 :=
  PeriodTorusHolomorphicCohomology.Dolbeault.inclusion p ≫ columnUnit0 p

theorem augmentation_d0 : D.augmentation ≫ D.d0 = 0 := by
  apply biprod.hom_ext
  · change D.augmentation ≫ D.categoryData.d0 ≫ biprod.fst = 0 ≫ biprod.fst
    rw [TotalCategory.Data.d0_fst, zero_comp]
    change (PeriodTorusHolomorphicCohomology.Dolbeault.inclusion p ≫ columnUnit0 p) ≫
      GodementExact.d0 (Derivation.smoothRingSheaf p) = 0
    have hz : columnUnit0 p ≫ GodementExact.d0 (Derivation.smoothRingSheaf p) = 0 :=
      GodementExact.augmentation_d0 (Derivation.smoothRingSheaf p)
    rw [Category.assoc, hz, comp_zero]
  · change D.augmentation ≫ D.categoryData.d0 ≫ biprod.snd = 0 ≫ biprod.snd
    rw [TotalCategory.Data.d0_snd, zero_comp]
    change (PeriodTorusHolomorphicCohomology.Dolbeault.inclusion p ≫ columnUnit0 p) ≫
      D.categoryData.h00 = 0
    rw [Category.assoc, D.columnUnit_d0, ← Category.assoc,
      PeriodTorusHolomorphicCohomology.Dolbeault.inclusion_differential, zero_comp]

abbrev initialComplex := ShortComplex.mk D.augmentation D.d0 D.augmentation_d0
abbrev oneComplex := D.categoryData.oneComplex
abbrev twoComplex := D.categoryData.twoComplex

/-- The original holomorphic-to-total augmentation is genuinely monomorphic. -/
theorem augmentation_mono : Mono D.augmentation := by
  let : Mono (PeriodTorusHolomorphicCohomology.Dolbeault.inclusion p) :=
    PeriodTorusHolomorphicCohomology.Dolbeault.inclusion_mono p
  let : Mono (columnUnit0 p) :=
    GodementExact.augmentation_mono (Derivation.smoothRingSheaf p)
  exact inferInstanceAs (Mono
    (PeriodTorusHolomorphicCohomology.Dolbeault.inclusion p ≫ columnUnit0 p))

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total.CompatibleOperators
