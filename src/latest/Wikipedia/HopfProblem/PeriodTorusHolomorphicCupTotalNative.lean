import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalExact
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupTotalInjective
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyBasic
import Wikipedia.HopfProblem.SheafCupProductResolutionCohomology

/-!
# Native holomorphic cohomology from the actual total resolution

The comparison is the genuine Ext-to-partial-resolution isomorphism,
followed by the original global biproduct and kernel/range comparisons.
No product compatibility or marked-coordinate identification is a premise.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total.CompatibleOperators

variable {p : PeriodDomain} (D : CompatibleOperators p)

/-- The original native torus H¹ compared with the actual total cochain quotient. -/
def nativeOneIso :
    AddCommGrpCat.of (PeriodTorusHolomorphicCohomology.H p 1) ≅
      AddCommGrpCat.of D.globalData.CohomologyOne := by
  letI : Injective D.partialResolution.I₀ := D.I0_injective
  exact D.partialResolution.h1Iso ≪≫ D.ringOperators.globalOneQuotientIso

/-- The original native torus H² compared with the actual total cochain quotient. -/
def nativeTwoIso :
    AddCommGrpCat.of (PeriodTorusHolomorphicCohomology.H p 2) ≅
      AddCommGrpCat.of D.globalData.CohomologyTwo := by
  letI : Injective D.partialResolution.I₀ := D.I0_injective
  letI : Injective D.partialResolution.I₁ := D.I1_injective
  exact D.partialResolution.h2Iso ≪≫ D.ringOperators.globalTwoQuotientIso

def nativeOneEquiv : PeriodTorusHolomorphicCohomology.H p 1 ≃+
    D.globalData.CohomologyOne := D.nativeOneIso.addCommGroupIsoToAddEquiv

def nativeTwoEquiv : PeriodTorusHolomorphicCohomology.H p 2 ≃+
    D.globalData.CohomologyTwo := D.nativeTwoIso.addCommGroupIsoToAddEquiv

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Total.CompatibleOperators
