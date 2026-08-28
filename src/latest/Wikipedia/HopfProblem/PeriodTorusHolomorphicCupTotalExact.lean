import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalColumns
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalTerms
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryExact

/-!
# Exactness of the genuine Godement--Dolbeault total resolution

The actual local Dolbeault primitives and the original Godement stalk
contractions give total primitives by the proved signed diagram chase.
The stalk criterion then gives exactness of the original sheaf maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total.CompatibleOperators

open SheafCupProduct

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {p : PeriodDomain} (D : CompatibleOperators p)

/-- Actual exactness at the original total degree-zero term. -/
theorem exact0 : D.initialComplex.Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact D.initialComplex).mpr
  intro x
  apply D.categoryData.map_initial_exact (GodementExact.additiveStalk x)
    D.augmentation D.augmentation_d0
  have hrow : Function.Exact
      ((GodementExact.additiveStalk x).map (Row.partialResolution p).ι).hom
      (D.stalkColumns x).d0 :=
    stalk_exact _ (Row.partialResolution p).exact₀ x
  have h := (D.stalkColumns x).exact_zero
    ((GodementExact.additiveStalk x).map (Row.partialResolution p).ι).hom hrow
  have haug : ((GodementExact.additiveStalk x).map D.augmentation).hom =
      (D.stalkColumns x).i0.comp
        ((GodementExact.additiveStalk x).map (Row.partialResolution p).ι).hom :=
    congrArg (fun f => f.hom)
      ((GodementExact.additiveStalk x).map_comp (Row.partialResolution p).ι
        (columnUnit0 p))
  exact haug.symm ▸ h

/-- Actual exactness at the original total degree-one term. -/
theorem exact1 : D.oneComplex.Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact D.oneComplex).mpr
  intro x
  apply D.categoryData.map_oneComplex_exact (GodementExact.additiveStalk x)
  exact (D.stalkColumns x).exact_one (stalk_exact _ (Row.partialResolution p).exact₁ x)

/-- Actual exactness at the original total degree-two term. -/
theorem exact2 : D.twoComplex.Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact D.twoComplex).mpr
  intro x
  apply D.categoryData.map_twoComplex_exact (GodementExact.additiveStalk x)
  exact (D.stalkColumns x).exact_two (stalk_exact _ (Row.partialResolution p).exact₂ x)

/-- A genuine partial resolution of the original torus holomorphic sheaf. -/
def partialResolution :
    SheafCupProductResolution.PartialResolution
      (TopCat.Sheaf AddCommGrpCat (TopCat.of p.Torus)) where
  F := PeriodTorusHolomorphicCohomology.holomorphicSheaf p
  I₀ := D.I0
  I₁ := D.I1
  I₂ := D.I2
  I₃ := D.I3
  ι := D.augmentation
  d₀ := D.d0
  d₁ := D.d1
  d₂ := D.d2
  ι_d₀ := D.augmentation_d0
  d₀_d₁ := D.categoryData.d0_d1
  d₁_d₂ := D.categoryData.d1_d2
  exact₀ := D.exact0
  exact₁ := D.exact1
  exact₂ := D.exact2
  mono_ι := D.augmentation_mono

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total.CompatibleOperators
