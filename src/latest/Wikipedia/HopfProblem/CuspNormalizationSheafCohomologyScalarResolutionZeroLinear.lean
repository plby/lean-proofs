import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsBiproduct

/-!
# Scalar naturality of actual Ext-zero and global sections
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafCohomology SheafCohomologyResolution SheafCohomologyGlobalSections

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
  (ρ : ℂ →+* End F) [Module ℂ (Sections F)]
  (hρ : ∀ (c : ℂ) (s : Sections F), (globalSectionsFunctor X).map (ρ c) s = c • s)

/-- For a genuine sheaf scalar action, the Ext-zero/global-section comparison is linear. -/
def h0PointwiseLinearEquiv :
    letI := cohomologyModule F ρ 0
    CategoryTheory.Sheaf.H.{0} F 0 ≃ₗ[ℂ] Sections F := by
  letI := cohomologyModule F ρ 0
  refine
    { __ := (h0GlobalIso F).addCommGroupIsoToAddEquiv
      map_smul' := ?_ }
  intro c a
  have h := ConcreteCategory.congr_hom (h0GlobalIso_naturality (ρ c)) a
  exact Eq.trans h (hρ c ((h0GlobalIso F).hom a))

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
