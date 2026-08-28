import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsResolution
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafNative
import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionRow
import Wikipedia.HopfProblem.SheafCupProductNativeBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalNativeMapsComposition

/-!
# Actual native cohomology maps of the first-column and last-row resolutions

The two genuine maps of partial resolutions induce the identity on the
original complex constant sheaf. Original partial-resolution naturality
therefore identifies their actual maps on global homology with the
original native Ext comparisons. The row uses its proved acyclicity;
the Godement and total terms use their proved injectivity.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalNativeMaps

open CuspNormalization SheafCupProduct SheafCupProductResolution

variable (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)

local instance constant_I0_injective :
    Injective (GodementExact.partialResolution (SheafConstants.complexSheaf X)).I₀ :=
  GodementRing.godement_injective_of_scalarEnd (SheafConstants.complexSheaf X)
    (constantScalarEnd X)

local instance constant_I1_injective :
    Injective (GodementExact.partialResolution (SheafConstants.complexSheaf X)).I₁ :=
  GodementRing.doubleGodement_injective_of_scalarEnd (SheafConstants.complexSheaf X)
    (constantScalarEnd X)

local instance total_I0_injective : Injective (TotalSheaf.partialResolution X hLC).I₀ :=
  TotalSheaf.I0_injective X

local instance total_I1_injective : Injective (TotalSheaf.partialResolution X hLC).I₁ :=
  TotalSheaf.I1_injective X

/-- The actual first-column map preserves the original native H¹ comparison. -/
theorem first_one_homology :
    (GodementExact.partialResolution (SheafConstants.complexSheaf X)).h1Iso.hom ≫
        ShortComplex.homologyMap (TotalMaps.first X hLC).globalOneMap =
      (TotalSheaf.partialResolution X hLC).h1Iso.hom := by
  have h := (TotalMaps.first X hLC).h1Iso_naturality
  exact h.symm.trans (map_identity_comp (CategoryTheory.Sheaf.functorH _ 1)
    (SheafConstants.complexAdditiveSheaf X) (TotalSheaf.partialResolution X hLC).h1Iso.hom)

/-- The actual first-column map preserves the original native H² comparison. -/
theorem first_two_homology :
    (GodementExact.partialResolution (SheafConstants.complexSheaf X)).h2Iso.hom ≫
        ShortComplex.homologyMap (TotalMaps.first X hLC).globalTwoMap =
      (TotalSheaf.partialResolution X hLC).h2Iso.hom := by
  have h := (TotalMaps.first X hLC).h2Iso_naturality
  exact h.symm.trans (map_identity_comp (CategoryTheory.Sheaf.functorH _ 2)
    (SheafConstants.complexAdditiveSheaf X) (TotalSheaf.partialResolution X hLC).h2Iso.hom)

variable [CompactSpace X] [T2Space X]

/-- The actual last-row map preserves the original H¹ comparison under proved row acyclicity. -/
theorem last_one_homology :
    (ResolutionRow.rowH1Iso X hLC).hom ≫
        ShortComplex.homologyMap (TotalMaps.last X hLC).globalOneMap =
      (TotalSheaf.partialResolution X hLC).h1Iso.hom := by
  let R := ResolutionRow.rowPartialResolution X hLC
  let T := TotalSheaf.partialResolution X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1) :=
    ResolutionRow.row_zero_one_subsingleton X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} T.I₀ 1) :=
    PartialResolution.injective_higher_subsingleton T.I₀ 0
  have h := (TotalMaps.last X hLC).h1IsoAcyclic_naturality
  have he : T.h1IsoAcyclic = T.h1Iso := T.h1IsoAcyclic_eq_h1Iso
  rw [he] at h
  exact h.symm.trans (map_identity_comp (CategoryTheory.Sheaf.functorH _ 1)
    (SheafConstants.complexAdditiveSheaf X) T.h1Iso.hom)

/-- The actual last-row map preserves the original H² comparison under proved row acyclicity. -/
theorem last_two_homology :
    (ResolutionRow.rowH2Iso X hLC).hom ≫
        ShortComplex.homologyMap (TotalMaps.last X hLC).globalTwoMap =
      (TotalSheaf.partialResolution X hLC).h2Iso.hom := by
  let R := ResolutionRow.rowPartialResolution X hLC
  let T := TotalSheaf.partialResolution X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 1) :=
    ResolutionRow.row_zero_one_subsingleton X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₀ 2) :=
    ResolutionRow.row_zero_two_subsingleton X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} R.I₁ 1) :=
    ResolutionRow.row_one_one_subsingleton X hLC
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} T.I₀ 1) :=
    PartialResolution.injective_higher_subsingleton T.I₀ 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} T.I₀ 2) :=
    PartialResolution.injective_higher_subsingleton T.I₀ 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} T.I₁ 1) :=
    PartialResolution.injective_higher_subsingleton T.I₁ 0
  have h := (TotalMaps.last X hLC).h2IsoAcyclic_naturality
  have he : T.h2IsoAcyclic = T.h2Iso := T.h2IsoAcyclic_eq_h2Iso
  rw [he] at h
  exact h.symm.trans (map_identity_comp (CategoryTheory.Sheaf.functorH _ 2)
    (SheafConstants.complexAdditiveSheaf X) T.h2Iso.hom)

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalNativeMaps
