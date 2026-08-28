import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic

/-!
# Restricting a complex manifold's scalar field

The original charts of a complex manifold are real smooth (indeed real
analytic when the complex charts are analytic). Only the scalar field
of the differentiability condition changes; no new atlas is chosen.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M]

/-- Complex chart compatibility gives real chart compatibility for the
same actual atlas. -/
theorem complexManifold_isRealManifold (n : ℕ∞ω) [IsManifold 𝓘(ℂ, E) n M] :
    IsManifold 𝓘(ℝ, E) n M := by
  apply isManifold_of_contDiffOn 𝓘(ℝ, E) n M
  intro e e' he he'
  have h := (contDiffGroupoid n 𝓘(ℂ, E)).compatible he he'
  have hc : ContDiffOn ℂ n (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
    simpa only [contDiffPregroupoid, mfld_simps] using h.1
  simpa only [mfld_simps] using hc.restrict_scalars ℝ

end Wikipedia.HopfProblem
