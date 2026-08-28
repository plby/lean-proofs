import Wikipedia.HopfProblem.SheafSingularCupComparisonMultiplicativeBasic
import Wikipedia.HopfProblem.SheafSingularCupComparisonPairingBridge

/-!
# Multiplicativity of the original constant-sheaf/singular comparison

Both products map to the same literal Alexander--Whitney product in the
genuine total resolution. Its proved native cohomology comparison is
injective, so the original sheaf/singular comparison preserves the
degree-one cup product. No multiplicative comparison is assumed.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison

open CuspNormalization SheafCupProduct ConstantSheafSingularComparison

variable (X : TopCat.{0}) [CompactSpace X] [T2Space X]
  (hLC : LocallyContractibleSpace X)

/-- The original native constant-complex-sheaf comparison preserves H¹ × H¹ → H². -/
theorem complexSheafH2Equiv_cup
    (a b : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1) :
    complexSheafH2Equiv X hLC (constantCup X a b) =
      Singular.cupProduct X (complexSheafH1Equiv X hLC a) (complexSheafH1Equiv X hLC b) :=
  pairing_comparison (complexSheafH1Equiv X hLC)
    (complexSheafH2Equiv X hLC).toEquiv
    (TotalSheaf.nativeOneEquiv X hLC) (TotalSheaf.nativeTwoEquiv X hLC)
    (fun c => TotalMaps.lastH1 X (RowGlobal.unitOne X c))
    (fun c => TotalMaps.lastH2 X (RowGlobal.unitTwo X c))
    (TotalSheaf.nativeTwoEquiv X hLC).injective
    (comparison_total_one X hLC) (comparison_total_two X hLC)
    (fun c d => constantCup X c d) (fun c d => Singular.cupProduct X c d)
    (fun c d => (TotalSheaf.globalData X).cup c d)
    (native_total_cup X hLC) (singular_total_cup X) a b

/-- The same statement for the original categorical comparison morphisms. -/
theorem complexSheafH2Iso_cup
    (a b : CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1) :
    (complexSheafH2Iso X hLC).hom (constantCup X a b) =
      Singular.cupProduct X
        ((complexSheafH1Iso X hLC).hom a) ((complexSheafH1Iso X hLC).hom b) :=
  complexSheafH2Equiv_cup X hLC a b

end Wikipedia.HopfProblem.SheafSingularCupComparison
