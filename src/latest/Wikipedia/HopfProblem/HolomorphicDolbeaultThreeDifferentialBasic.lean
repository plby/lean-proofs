import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFunctions
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBundle
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The real differential as an actual native cotangent section

This is the manifold Fréchet derivative of the literal smooth section,
with values in the original real cotangent Hom bundle.  Its smoothness
comes from Mathlib's derivative theorem in the actual tangent coordinates.
-/

noncomputable section

open Bundle Set TopologicalSpace Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

local notation "IR" => modelWithCornersSelf ℝ E
local notation "IR₁" => modelWithCornersSelf ℝ ℂ

/-- The actual derivative in the original tangent fibre at each point. -/
def realSection (U : Opens M) (s : Functions.SmoothSection E M U)
    (x : U) : Forms.Covector E M (x : M) :=
  mfderiv IR IR₁ (Functions.extend E M U s) (x : M)

/-- The usual derivative coordinates and the native cotangent Hom-bundle
coordinates agree literally; the target tangent charts are the original
identity charts of the complex line. -/
theorem realSection_inCoordinates (U : Opens M) (s : Functions.SmoothSection E M U)
    (x₀ : M) (x : U) :
    Forms.inCoordinates E M (realSection E M U s) x₀ x =
      inTangentCoordinates IR IR₁ id (Functions.extend E M U s)
        (mfderiv IR IR₁ (Functions.extend E M U s)) x₀ (x : M) := by
  ext v
  rw [Forms.inCoordinates_apply]
  simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space]
  rfl

/-- The real differential is smooth as a section of the unchanged
native cotangent bundle, not as a falsely constant family of covectors. -/
theorem realSection_smooth (U : Opens M) (s : Functions.SmoothSection E M U) :
    ContMDiff IR ((𝓘(ℝ, E)).prod 𝓘(ℝ, E →L[ℝ] ℂ)) ∞
      (Forms.sectionMap E M (realSection E M U s)) := by
  intro x
  apply (Forms.smoothSectionAt_iff E M (realSection E M U s) x).mpr
  have h := (Functions.extend_contMDiffAt E M U s x x.property).mfderiv_const
    (m := ∞) (by simp)
  have hs := h.comp x (contMDiff_subtype_val x)
  have he : Forms.inCoordinates E M (realSection E M U s) (x : M) =
      fun y : U => inTangentCoordinates IR IR₁ id (Functions.extend E M U s)
        (mfderiv IR IR₁ (Functions.extend E M U s)) (x : M) (y : M) :=
    funext (realSection_inCoordinates E M U s x)
  rw [he]
  exact hs

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Literal restriction of functions restricts the original differential. -/
theorem realSection_restrict {U V : Opens M} (h : U ≤ V)
    (s : Functions.SmoothSection E M V) (x : U) :
    realSection E M U (Functions.restriction E M h s) x =
      realSection E M V s ⟨(x : M), h x.property⟩ := by
  exact (Functions.extend_restrict_germ E M h s x x.property).mfderiv_eq

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- At the preferred native chart centre the genuine manifold derivative
is the real Fréchet derivative of the literal chart representative. -/
theorem realSection_eq_chart_fderiv (U : Opens M)
    (s : Functions.SmoothSection E M U) (x : U) :
    Forms.covectorAsModel E M (realSection E M U s x) =
      fderiv ℝ (Functions.extend E M U s ∘ (chartAt E (x : M)).symm)
        (chartAt E (x : M) (x : M)) := by
  have h := (Functions.extend_contMDiffAt E M U s x x.property).mdifferentiableAt
    (show ∞ ≠ (0 : ℕ∞ω) by simp)
  simpa [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
    realSection, Forms.covectorAsModel, chartAt_self_eq] using! h.mfderiv

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.NativeDifferential
