import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafExact
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafInjective
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafGlobal
import Wikipedia.HopfProblem.SheafCupProductResolutionCohomology

/-!
# Genuine native sheaf cohomology from the actual total resolution

The comparison is the previously proved Ext-to-partial-resolution map,
followed by the canonical global biproduct and kernel/range comparisons.
No product compatibility or cohomology identification is an input.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf

open CuspNormalization

variable (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)

/-- Original native constant-sheaf H¹ as the genuine total coface quotient. -/
def nativeOneIso :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1) ≅
      AddCommGrpCat.of (globalData X).CohomologyOne := by
  letI : Injective (partialResolution X hLC).I₀ := I0_injective X
  exact (partialResolution X hLC).h1Iso ≪≫ globalOneQuotientIso X

/-- Original native constant-sheaf H² as the genuine total coface quotient. -/
def nativeTwoIso :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 2) ≅
      AddCommGrpCat.of (globalData X).CohomologyTwo := by
  letI : Injective (partialResolution X hLC).I₀ := I0_injective X
  letI : Injective (partialResolution X hLC).I₁ := I1_injective X
  exact (partialResolution X hLC).h2Iso ≪≫ globalTwoQuotientIso X

def nativeOneEquiv :
    CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 1 ≃+
      (globalData X).CohomologyOne := (nativeOneIso X hLC).addCommGroupIsoToAddEquiv

def nativeTwoEquiv :
    CategoryTheory.Sheaf.H.{0} (SheafConstants.complexAdditiveSheaf X) 2 ≃+
      (globalData X).CohomologyTwo := (nativeTwoIso X hLC).addCommGroupIsoToAddEquiv

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalSheaf
