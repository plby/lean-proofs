import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafColumns
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafTerms
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryExact
import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionRowExact

/-!
# Exactness of the genuine Godement--singular total resolution

At every actual stalk, the original Godement columns are exact and the
original singular-cochain row is locally exact. The proved signed-total
diagram chase gives actual stalk primitives. The genuine stalk criterion
then proves exactness of the original sheaf total complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf

open SheafCupProduct

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (X : TopCat.{0})

/-- The original total augmentation is monomorphic. -/
theorem augmentation_mono : Mono (augmentation X) := by
  let : Mono (ResolutionRow.rowAugmentation X) := ResolutionRow.rowAugmentation_mono X
  change Mono (ResolutionRow.rowAugmentation X ≫ columnUnit X 0)
  infer_instance

/-- Actual exactness at the original degree-zero total term. -/
theorem exact0 (hLC : LocallyContractibleSpace X) : (initialComplex X).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (initialComplex X)).mpr
  intro x
  apply (categoryData X).map_initial_exact (GodementExact.additiveStalk x)
    (augmentation X) (augmentation_d0 X)
  have hrow : Function.Exact
      ((GodementExact.additiveStalk x).map (ResolutionRow.rowAugmentation X)).hom
      (stalkColumns X x).d0 :=
    ((ResolutionRow.rowInitialComplex X).map
      (GodementExact.additiveStalk x)).ab_exact_iff_function_exact.mp
        ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
          (ResolutionRow.rowInitialComplex X)).mp
            (ResolutionRow.rowInitialComplex_exact X hLC) x)
  have h := (stalkColumns X x).exact_zero
    ((GodementExact.additiveStalk x).map (ResolutionRow.rowAugmentation X)).hom hrow
  have haug : ((GodementExact.additiveStalk x).map (augmentation X)).hom =
      (stalkColumns X x).i0.comp
        ((GodementExact.additiveStalk x).map (ResolutionRow.rowAugmentation X)).hom :=
    congrArg (fun f => f.hom)
      ((GodementExact.additiveStalk x).map_comp (ResolutionRow.rowAugmentation X)
        (columnUnit X 0))
  exact haug.symm ▸ h

/-- Actual exactness at the original degree-one total term. -/
theorem exact1 (hLC : LocallyContractibleSpace X) : (oneComplex X).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (oneComplex X)).mpr
  intro x
  apply (categoryData X).map_oneComplex_exact (GodementExact.additiveStalk x)
  apply (stalkColumns X x).exact_one
  exact ((ResolutionRow.rowOneComplex X).map
      (GodementExact.additiveStalk x)).ab_exact_iff_function_exact.mp
    ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
      (ResolutionRow.rowOneComplex X)).mp (ResolutionRow.rowOneComplex_exact X hLC) x)

/-- Actual exactness at the original degree-two total term. -/
theorem exact2 (hLC : LocallyContractibleSpace X) : (twoComplex X).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (twoComplex X)).mpr
  intro x
  apply (categoryData X).map_twoComplex_exact (GodementExact.additiveStalk x)
  apply (stalkColumns X x).exact_two
  exact ((ResolutionRow.rowTwoComplex X).map
      (GodementExact.additiveStalk x)).ab_exact_iff_function_exact.mp
    ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
      (ResolutionRow.rowTwoComplex X)).mp (ResolutionRow.rowTwoComplex_exact X hLC) x)

/-- The original constant sheaf has this genuine partial injective
resolution. Every exactness assertion has been proved on actual stalks. -/
def partialResolution (hLC : LocallyContractibleSpace X) :
    SheafCupProductResolution.PartialResolution (TopCat.Sheaf AddCommGrpCat.{0} X) where
  F := CuspNormalization.SheafConstants.complexAdditiveSheaf X
  I₀ := I0 X
  I₁ := I1 X
  I₂ := I2 X
  I₃ := I3 X
  ι := augmentation X
  d₀ := d0 X
  d₁ := d1 X
  d₂ := d2 X
  ι_d₀ := augmentation_d0 X
  d₀_d₁ := (categoryData X).d0_d1
  d₁_d₂ := (categoryData X).d1_d2
  exact₀ := exact0 X hLC
  exact₁ := exact1 X hLC
  exact₂ := exact2 X hLC
  mono_ι := augmentation_mono X

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf
