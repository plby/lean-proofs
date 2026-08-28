import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalNativeMapsBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsQuotientHomology

/-!
# The first-column quotient map is the original native total comparison

The source is the original multiplicative Godement comparison for the
original constant complex ring sheaf. The target is the original native
comparison of the actual total resolution. Their equality follows from
the actual resolution map and the canonical quotient-map square.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalNativeMaps

open CuspNormalization SheafCupProduct

variable (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)

/-- The actual first-column quotient map preserves the original native H¹ identification. -/
theorem first_h1_native :
    (h1CofaceIso (SheafConstants.complexSheaf X) (constantScalarEnd X)).hom ≫
        AddCommGrpCat.ofHom (TotalMaps.firstH1 X) =
      (TotalSheaf.nativeOneIso X hLC).hom := by
  let R := GodementExact.partialResolution (SheafConstants.complexSheaf X)
  let T := TotalSheaf.partialResolution X hLC
  let : Injective R.I₀ := constant_I0_injective X
  let : Injective T.I₀ := total_I0_injective X hLC
  exact postcompose_comparison R.h1Iso.hom T.h1Iso.hom
    (SheafCupProductResolution.Coface.oneHomologyIso
      (globalData (SheafConstants.complexSheaf X))).hom
    (TotalSheaf.globalOneQuotientIso X).hom
    (ShortComplex.homologyMap (TotalMaps.first X hLC).globalOneMap)
    (AddCommGrpCat.ofHom (TotalMaps.firstH1 X))
    (first_one_homology X hLC) (TotalMaps.firstH1_homology X hLC)

/-- The actual first-column quotient map preserves the original native H² identification. -/
theorem first_h2_native :
    (h2CofaceIso (SheafConstants.complexSheaf X) (constantScalarEnd X)).hom ≫
        AddCommGrpCat.ofHom (TotalMaps.firstH2 X) =
      (TotalSheaf.nativeTwoIso X hLC).hom := by
  let R := GodementExact.partialResolution (SheafConstants.complexSheaf X)
  let T := TotalSheaf.partialResolution X hLC
  let : Injective R.I₀ := constant_I0_injective X
  let : Injective R.I₁ := constant_I1_injective X
  let : Injective T.I₀ := total_I0_injective X hLC
  let : Injective T.I₁ := total_I1_injective X hLC
  exact postcompose_comparison R.h2Iso.hom T.h2Iso.hom
    (SheafCupProductResolution.Coface.twoHomologyIso
      (globalData (SheafConstants.complexSheaf X))).hom
    (TotalSheaf.globalTwoQuotientIso X).hom
    (ShortComplex.homologyMap (TotalMaps.first X hLC).globalTwoMap)
    (AddCommGrpCat.ofHom (TotalMaps.firstH2 X))
    (first_two_homology X hLC) (TotalMaps.firstH2_homology X hLC)

/-- The first-column comparison on each original native degree-one class. -/
theorem first_h1_native_apply
    (a : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1) :
    TotalMaps.firstH1 X
        (h1CofaceEquiv (SheafConstants.complexSheaf X) (constantScalarEnd X) a) =
      TotalSheaf.nativeOneEquiv X hLC a :=
  ConcreteCategory.congr_hom (first_h1_native X hLC) a

/-- The first-column comparison on each original native degree-two class. -/
theorem first_h2_native_apply
    (a : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 2) :
    TotalMaps.firstH2 X
        (h2CofaceEquiv (SheafConstants.complexSheaf X) (constantScalarEnd X) a) =
      TotalSheaf.nativeTwoEquiv X hLC a :=
  ConcreteCategory.congr_hom (first_h2_native X hLC) a

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalNativeMaps
