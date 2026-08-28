import Wikipedia.HopfProblem.CuspNormalizationGermsNormalAlgebra
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalQuotient
import Wikipedia.HopfProblem.CuspNormalizationGermsRestriction

/-!
# Normality of the actual analytic branch-germ ring

The branch ring is the ring of actual holomorphic function germs on
complex two-space, not a polynomial or formal power-series substitute.
Integrality gives a locally uniform bound for a fraction. The proved
analytic quotient extension then puts that fraction back in the ring.
Thus the branch ring is integrally closed without any normality premise.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open ToricCharts

/-- The actual ring of holomorphic germs on a smooth two-dimensional
branch is integrally closed in its actual fraction field. -/
instance branchGerm_isIntegrallyClosed : IsIntegrallyClosed BranchGerm := by
  apply isIntegrallyClosed_of_analytic_quotient_extension
  intro f g hf hg hgerm M hbound
  exact exists_analytic_quotient_of_bounded hf hg hgerm hbound

/-- An integral fraction of actual analytic representatives has an
actual analytic factor, including on the denominator's zero set. -/
theorem exists_analytic_quotient_of_isIntegral
    {f g : CoordinateSpace 2 → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hgerm : ofAnalytic g hg ≠ 0)
    (hint : IsIntegral BranchGerm
      (algebraMap BranchGerm (FractionRing BranchGerm) (ofAnalytic f hf) /
        algebraMap BranchGerm (FractionRing BranchGerm) (ofAnalytic g hg))) :
    ∃ q : CoordinateSpace 2 → ℂ, AnalyticAt ℂ q 0 ∧
      f =ᶠ[𝓝 0] (fun z => g z * q z) := by
  obtain ⟨_, _, hbound⟩ :=
    exists_pos_eventually_norm_div_le_off_zero_of_isIntegral hf hg hgerm hint
  exact exists_analytic_quotient_of_bounded hf hg
    (fun hzero => hgerm ((ofAnalytic_eq_zero_iff g hg).mpr hzero)) hbound

/-- An element of the genuine branch fraction field is integral exactly
when it has a genuine analytic representative near the origin. -/
theorem isIntegral_fraction_iff_exists_analytic (x : FractionRing BranchGerm) :
    IsIntegral BranchGerm x ↔
      ∃ (f : CoordinateSpace 2 → ℂ) (hf : AnalyticAt ℂ f 0),
        algebraMap BranchGerm (FractionRing BranchGerm) (ofAnalytic f hf) = x := by
  constructor
  · intro hx
    obtain ⟨φ, hφ⟩ := (isIntegrallyClosed_iff (FractionRing BranchGerm)).mp
      branchGerm_isIntegrallyClosed hx
    obtain ⟨f, hf, rfl⟩ := exists_representative φ
    exact ⟨f, hf, hφ⟩
  · rintro ⟨f, hf, rfl⟩
    exact isIntegral_algebraMap

end Wikipedia.HopfProblem.CuspNormalization.Germs
