import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsBiproduct
import Wikipedia.HopfProblem.CuspNormalizationSheafCuspSums
import Wikipedia.HopfProblem.CuspNormalizationSheafEvaluationSheaf
import Mathlib.LinearAlgebra.Pi

/-!
# Actual global sections of the two scalar skyscrapers

The top open set contains each actual support point. The canonical
skyscraper-section isomorphism is its actual coefficient identification,
and the finite-sum comparison keeps the source order P, Q.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

open SheafCohomologyResolution SheafResolution CuspQuotient

variable {X : TopCat.{0}}

/-- Global sections of an actual scalar skyscraper are its actual coefficients. -/
def scalarSkyscraperGlobalAddEquiv (b : X) :
    Sections (SheafEvaluation.skyscraper b (AddCommGrpCat.of ℂ)) ≃+ ℂ :=
  (SheafEvaluation.skyscraperSectionIso b (AddCommGrpCat.of ℂ) ⊤ trivial).addCommGroupIsoToAddEquiv

/-- The canonical coefficientwise complex scalar action on actual skyscraper sections. -/
instance scalarSkyscraperSections_module (b : X) :
    Module ℂ (Sections (SheafEvaluation.skyscraper b (AddCommGrpCat.of ℂ))) :=
  (scalarSkyscraperGlobalAddEquiv b).module ℂ

/-- The actual skyscraper-section coefficient comparison is complex linear. -/
def scalarSkyscraperGlobalLinearEquiv (b : X) :
    Sections (SheafEvaluation.skyscraper b (AddCommGrpCat.of ℂ)) ≃ₗ[ℂ] ℂ :=
  (scalarSkyscraperGlobalAddEquiv b).linearEquiv ℂ

@[simp] theorem scalarSkyscraperGlobalLinearEquiv_apply (b : X)
    (s : Sections (SheafEvaluation.skyscraper b (AddCommGrpCat.of ℂ))) :
    scalarSkyscraperGlobalLinearEquiv b s =
      (SheafEvaluation.skyscraperSectionIso b (AddCommGrpCat.of ℂ) ⊤ trivial).hom s := rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The original coefficient action on either actual triple-point summand. -/
instance triplePointSections_module (t : Fin 2) :
    Module ℂ (Sections (triplePointSheaf C ε hε t)) :=
  scalarSkyscraperSections_module (X := TopCat.of (CentralSpace C ε)) (triplePoint C ε hε t)

/-- The genuine coefficient comparison at the actual point P or Q. -/
def triplePointGlobalLinearEquiv (t : Fin 2) : Sections (triplePointSheaf C ε hε t) ≃ₗ[ℂ] ℂ :=
  scalarSkyscraperGlobalLinearEquiv (X := TopCat.of (CentralSpace C ε)) (triplePoint C ε hε t)

/-- Actual direct-sum sections have their pointwise complex module. -/
instance tripleSections_module : Module ℂ (Sections (tripleSheaf C ε hε)) :=
  finiteSectionsModule (triplePointSheaf C ε hε)

/-- The actual last global-section term is complex-linearly ℂ², in
the literal source order P, Q. -/
def tripleGlobalLinearEquiv : Sections (tripleSheaf C ε hε) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (finiteSectionsLinearEquiv (triplePointSheaf C ε hε)).trans
    (LinearEquiv.piCongrRight fun t => triplePointGlobalLinearEquiv C ε hε t)

/-- Each coordinate is the actual sheaf projection followed by the
actual coefficient identification at its specified triple point. -/
@[simp] theorem tripleGlobalLinearEquiv_apply (s : Sections (tripleSheaf C ε hε)) (t : Fin 2) :
    tripleGlobalLinearEquiv C ε hε s t =
      triplePointGlobalLinearEquiv C ε hε t
        ((globalSectionsFunctor (TopCat.of (CentralSpace C ε))).map
          (biproduct.π (triplePointSheaf C ε hε) t) s) := by
  change triplePointGlobalLinearEquiv C ε hε t
    (finiteSectionsEquiv (triplePointSheaf C ε hε) s t) = _
  rw [finiteSectionsEquiv_apply]

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
