import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Real and complex tangent transitions in the same original atlas

On actual chart overlaps, the real tangent transition is the scalar
restriction of the complex tangent transition. This compares the genuine
derivatives used by the two native tangent bundles, without changing any
chart or introducing a new bundle topology.
-/

noncomputable section

open Set Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Tangent

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ω M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original real tangent change on a genuine chart overlap is the
restriction of scalars of the original complex tangent change. -/
theorem tangentCoordChange_restrictScalars (x y z : M)
    (hx : z ∈ (chartAt E x).source) (hy : z ∈ (chartAt E y).source) :
    tangentCoordChange 𝓘(ℝ, E) x y z =
      (tangentCoordChange 𝓘(ℂ, E) x y z).restrictScalars ℝ := by
  have hc := hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℂ, E))
    (x := x) (y := y) (z := z) (by simpa using (show
      z ∈ (chartAt E x).source ∩ (chartAt E y).source from ⟨hx, hy⟩))
  have hr := hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℝ, E))
    (x := x) (y := y) (z := z) (by simpa using (show
      z ∈ (chartAt E x).source ∩ (chartAt E y).source from ⟨hx, hy⟩))
  have hc' : HasFDerivAt ((chartAt E y) ∘ (chartAt E x).symm)
      (tangentCoordChange 𝓘(ℂ, E) x y z) (chartAt E x z) := by
    simpa only [mfld_simps, hasFDerivWithinAt_univ] using hc
  have hr' : HasFDerivAt ((chartAt E y) ∘ (chartAt E x).symm)
      (tangentCoordChange 𝓘(ℝ, E) x y z) (chartAt E x z) := by
    simpa only [mfld_simps, hasFDerivWithinAt_univ] using hr
  exact hr'.unique (hc'.restrictScalars ℝ)

/-- Thus the actual real tangent change commutes with the original
complex scalar action on the model, on its actual overlap. -/
theorem tangentCoordChange_complex_smul (x y z : M)
    (hx : z ∈ (chartAt E x).source) (hy : z ∈ (chartAt E y).source)
    (c : ℂ) (v : E) :
    tangentCoordChange 𝓘(ℝ, E) x y z (c • v) =
      c • tangentCoordChange 𝓘(ℝ, E) x y z v := by
  rw [tangentCoordChange_restrictScalars E M x y z hx hy]
  exact (tangentCoordChange 𝓘(ℂ, E) x y z).map_smul c v

/-- The same exact comparison for the original inverse tangent
trivializations. The displayed model identification is only the defining
type synonym of a tangent fibre, not a replacement topology. -/
theorem symmL_trivializationAt_restrictScalars (x₀ x : M)
    (hx : x ∈ (chartAt E x₀).source) :
    (show E →L[ℝ] E from
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ x) =
    (show E →L[ℂ] E from
      (trivializationAt E (TangentSpace 𝓘(ℂ, E)) x₀).symmL ℂ x).restrictScalars ℝ := by
  rw [TangentBundle.symmL_trivializationAt_eq_core hx,
    TangentBundle.symmL_trivializationAt_eq_core hx]
  exact tangentCoordChange_restrictScalars E M x₀ x x hx
    (ChartedSpace.mem_chart_source (H := E) x)

/-- The native real inverse tangent trivialization commutes with all
original complex model scalars on its genuine chart domain. -/
theorem symmL_trivializationAt_complex_smul (x₀ x : M)
    (hx : x ∈ (chartAt E x₀).source) (c : ℂ) (v : E) :
    (show E from (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ x (c • v)) =
      c • (show E from
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ x v) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core hx]
  exact tangentCoordChange_complex_smul E M x₀ x x hx
    (ChartedSpace.mem_chart_source (H := E) x) c v

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Tangent
