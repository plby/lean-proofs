import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstMapsNativeBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstMapsHomology

/-!
# The original native comparison equals the actual first-column quotient map

These are the canonical degree-one and degree-two comparison squares,
obtained from the original resolution and original homology maps.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps

open SheafCupProduct

variable (p : PeriodDomain)

theorem firstOne_native :
    (h1CofaceIso (Derivation.holomorphicRingSheaf p) (sourceScalarEnd p)).hom ≫
        AddCommGrpCat.ofHom (firstH1 p) = (totalOperators p).nativeOneIso.hom := by
  let R := GodementExact.partialResolution (Derivation.holomorphicRingSheaf p)
  let T := totalPartialResolution p
  let : Injective R.I₀ := source_I0_injective p
  let : Injective T.I₀ := total_I0_injective p
  exact SheafSingularCupComparison.TotalNativeMaps.postcompose_comparison
    R.h1Iso.hom T.h1Iso.hom
    (SheafCupProductResolution.Coface.oneHomologyIso (sourceData p)).hom
    (totalOperators p).ringOperators.globalOneQuotientIso.hom
    (ShortComplex.homologyMap (firstToTotal p).globalOneMap)
    (AddCommGrpCat.ofHom (firstH1 p)) (first_one_homology p) (firstH1_homology p)

theorem firstTwo_native :
    (h2CofaceIso (Derivation.holomorphicRingSheaf p) (sourceScalarEnd p)).hom ≫
        AddCommGrpCat.ofHom (firstH2 p) = (totalOperators p).nativeTwoIso.hom := by
  let R := GodementExact.partialResolution (Derivation.holomorphicRingSheaf p)
  let T := totalPartialResolution p
  let : Injective R.I₀ := source_I0_injective p
  let : Injective R.I₁ := source_I1_injective p
  let : Injective T.I₀ := total_I0_injective p
  let : Injective T.I₁ := total_I1_injective p
  exact SheafSingularCupComparison.TotalNativeMaps.postcompose_comparison
    R.h2Iso.hom T.h2Iso.hom
    (SheafCupProductResolution.Coface.twoHomologyIso (sourceData p)).hom
    (totalOperators p).ringOperators.globalTwoQuotientIso.hom
    (ShortComplex.homologyMap (firstToTotal p).globalTwoMap)
    (AddCommGrpCat.ofHom (firstH2 p)) (first_two_homology p) (firstH2_homology p)

private theorem comparison_apply {A B C : AddCommGrpCat.{0}}
    (e : A ≅ B) (f : A ≅ C) (g : B ⟶ C) (h : e.hom ≫ g = f.hom) (a : A) :
    g (e.addCommGroupIsoToAddEquiv a) = f.addCommGroupIsoToAddEquiv a :=
  ConcreteCategory.congr_hom h a

theorem firstOne_native_apply (a : PeriodTorusHolomorphicCohomology.H p 1) :
    firstH1 p (h1CofaceEquiv (Derivation.holomorphicRingSheaf p) (sourceScalarEnd p) a) =
      totalNativeOneEquiv p a :=
  comparison_apply (h1CofaceIso (Derivation.holomorphicRingSheaf p) (sourceScalarEnd p))
    (totalOperators p).nativeOneIso (AddCommGrpCat.ofHom (firstH1 p)) (firstOne_native p) a

theorem firstTwo_native_apply (a : PeriodTorusHolomorphicCohomology.H p 2) :
    firstH2 p (h2CofaceEquiv (Derivation.holomorphicRingSheaf p) (sourceScalarEnd p) a) =
      totalNativeTwoEquiv p a :=
  comparison_apply (h2CofaceIso (Derivation.holomorphicRingSheaf p) (sourceScalarEnd p))
    (totalOperators p).nativeTwoIso (AddCommGrpCat.ofHom (firstH2 p)) (firstTwo_native p) a

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps
