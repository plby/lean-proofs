import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsCurves
import Mathlib.LinearAlgebra.Pi

/-!
# Actual global sections of the three source-ordered double curves

The comparison uses the actual categorical sheaf projections, followed
by evaluation of actual global holomorphic functions on the three
constructed curves. The source order is preserved.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

open SheafCohomologyResolution SheafResolution CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual finite-sum global sections carry the original
pointwise complex action on their three actual sheaf projections. -/
instance boundarySections_module : Module ℂ (Sections (boundarySheaf C ε hε hε1 hC hR)) :=
  finiteSectionsModule (curveSheaf C ε hε hε1 hC hR)

/-- Actual boundary global sections are complex-linearly ℂ³ in the
source order of the actual double curves. -/
def boundaryGlobalLinearEquiv : Sections (boundarySheaf C ε hε hε1 hC hR) ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  (finiteSectionsLinearEquiv (curveSheaf C ε hε hε1 hC hR)).trans
    (LinearEquiv.piCongrRight fun k => curveGlobalLinearEquiv C ε hε hε1 hC hR k)

/-- Each scalar is actual evaluation of the corresponding genuine
global section obtained through the actual categorical projection. -/
@[simp] theorem boundaryGlobalLinearEquiv_apply
    (s : Sections (boundarySheaf C ε hε hε1 hC hR)) (k : Fin 3) :
    boundaryGlobalLinearEquiv C ε hε hε1 hC hR s k =
      curveGlobalLinearEquiv C ε hε hε1 hC hR k
        ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
          (biproduct.π (curveSheaf C ε hε hε1 hC hR) k) s) := by
  change curveGlobalLinearEquiv C ε hε hε1 hC hR k
    (finiteSectionsEquiv (curveSheaf C ε hε hε1 hC hR) s k) = _
  rw [finiteSectionsEquiv_apply]

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
