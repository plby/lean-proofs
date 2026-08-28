import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeTangentTransitions
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBundle

/-!
# Antiholomorphic projection in native cotangent coordinates

The original inverse tangent trivialization commutes with complex
scalars on its actual chart domain. Consequently the native Hom-bundle
coordinate map commutes with the pointwise antiholomorphic projection.
The covectors and coordinates are the original `Forms` bundle objects.
-/

noncomputable section

open Set Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Tangent

section Covectors

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

/-- Antiholomorphic projection commutes with an actual real-linear
pullback that respects the original complex structures. -/
theorem antiPart_comp_of_complexStructure (L : F →L[ℝ] ℂ) (T : E →L[ℝ] F)
    (hT : ∀ v, T (Complex.I • v) = Complex.I • T v) :
    antiPart (L.comp T) = (antiPart L).comp T := by
  ext v
  simp only [antiPart_apply, ContinuousLinearMap.comp_apply, hT]

end Covectors

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- In the genuine native cotangent Hom-bundle coordinates on their
original chart domain, pointwise antiholomorphic projection is exactly
the fixed antiholomorphic projection of the original coordinate covector. -/
theorem inCoordinates_antiPart {U : Opens M}
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x₀ : M) (x : U)
    (hx : (x : M) ∈ (chartAt E x₀).source) :
    Forms.inCoordinates E M
      (fun y => Forms.covectorFromModel E M (y : M)
        (antiPart (Forms.covectorAsModel E M (a y)))) x₀ x =
      antiPart (Forms.inCoordinates E M a x₀ x) := by
  ext v
  rw [Forms.inCoordinates_apply E M
    (fun y : U => Forms.covectorFromModel E M (y : M)
      (antiPart (Forms.covectorAsModel E M (a y)))) x₀ x v]
  simp only [Forms.inCoordinates_apply, Forms.covectorFromModel,
    Forms.covectorAsModel, antiPart_apply,
    symmL_trivializationAt_complex_smul E M x₀ (x : M) hx Complex.I v]
  exact antiPart_apply (Forms.covectorAsModel E M (a x))
    (show E from
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ (x : M) v)

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Tangent
