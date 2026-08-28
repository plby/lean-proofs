import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalNativeMapsFirst
import Wikipedia.HopfProblem.SheafSingularCupComparisonRowGlobalBasic

/-!
# The last-row quotient map is the original native total comparison

The source is the actual ring-cochain row with its proved acyclicity.
The canonical row quotient isomorphism and the actual map into the total
resolution give exactly the original native total comparison. No cup
compatibility or choice of a comparison is an assumption.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalNativeMaps

open CuspNormalization

variable (X : TopCat.{0}) [CompactSpace X] [T2Space X]
  (hLC : LocallyContractibleSpace X)

/-- The actual last-row quotient map preserves the original native H¹ identification. -/
theorem last_h1_native :
    ((ResolutionRow.rowH1Iso X hLC).hom ≫ (RowGlobal.oneHomologyIso X).hom) ≫
        AddCommGrpCat.ofHom (TotalMaps.lastH1 X) =
      (TotalSheaf.nativeOneIso X hLC).hom := by
  let T := TotalSheaf.partialResolution X hLC
  let : Injective T.I₀ := total_I0_injective X hLC
  exact postcompose_comparison (ResolutionRow.rowH1Iso X hLC).hom T.h1Iso.hom
    (RowGlobal.oneHomologyIso X).hom (TotalSheaf.globalOneQuotientIso X).hom
    (ShortComplex.homologyMap (TotalMaps.last X hLC).globalOneMap)
    (AddCommGrpCat.ofHom (TotalMaps.lastH1 X))
    (last_one_homology X hLC) (TotalMaps.lastH1_homology X hLC)

/-- The actual last-row quotient map preserves the original native H² identification. -/
theorem last_h2_native :
    ((ResolutionRow.rowH2Iso X hLC).hom ≫ (RowGlobal.twoHomologyIso X).hom) ≫
        AddCommGrpCat.ofHom (TotalMaps.lastH2 X) =
      (TotalSheaf.nativeTwoIso X hLC).hom := by
  let T := TotalSheaf.partialResolution X hLC
  let : Injective T.I₀ := total_I0_injective X hLC
  let : Injective T.I₁ := total_I1_injective X hLC
  exact postcompose_comparison (ResolutionRow.rowH2Iso X hLC).hom T.h2Iso.hom
    (RowGlobal.twoHomologyIso X).hom (TotalSheaf.globalTwoQuotientIso X).hom
    (ShortComplex.homologyMap (TotalMaps.last X hLC).globalTwoMap)
    (AddCommGrpCat.ofHom (TotalMaps.lastH2 X))
    (last_two_homology X hLC) (TotalMaps.lastH2_homology X hLC)

/-- The last-row comparison on each original native degree-one class. -/
theorem last_h1_native_apply
    (a : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1) :
    TotalMaps.lastH1 X
        (RowGlobal.oneHomologyEquiv X ((ResolutionRow.rowH1Iso X hLC).hom a)) =
      TotalSheaf.nativeOneEquiv X hLC a :=
  ConcreteCategory.congr_hom (last_h1_native X hLC) a

/-- The last-row comparison on each original native degree-two class. -/
theorem last_h2_native_apply
    (a : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 2) :
    TotalMaps.lastH2 X
        (RowGlobal.twoHomologyEquiv X ((ResolutionRow.rowH2Iso X hLC).hom a)) =
      TotalSheaf.nativeTwoEquiv X hLC a :=
  ConcreteCategory.congr_hom (last_h2_native X hLC) a

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalNativeMaps
