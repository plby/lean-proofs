import Wikipedia.HopfProblem.DegreeCollapseCubicFlowCylinder
import Wikipedia.HopfProblem.DegreeCollapseSignedTransversePlanes
import Wikipedia.HopfProblem.DegreeCollapseActualEndpointBasins

/-!
# Exact two-block basin equations on actual cubic endpoint slices

The explicit cubic flow cylinder multiplies each transverse coordinate
by a nonzero exponential. Hence its signed zero planes are unchanged.
The original signed splitting converts the proved native endpoint basins
into the literal two-block planes used in the corrected cylinder.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ}

theorem cubicFlowCylinder_transverse_zero_iff (σ : Fin m → ℝ) (a T : ℝ)
    (z : Fin m → ℝ) (i : Fin m) :
    (cubicFlowCylinder σ a (z, T)).2 i = 0 ↔ z i = 0 := by
  simp [cubicFlowCylinder, Real.exp_ne_zero]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

open Classical in
theorem incoming_cubic_slice_basin (σ : Fin m → ℝ) (a T : ℝ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (F : Flow ℝ M) {p : M}
    (hbasin : ∀ z ∈ Φ.source, Tendsto (fun t => F t (Φ z)) atTop (𝓝 p) ↔
      ∀ i, σ i = -1 → z.2 i = 0)
    (u : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
    (hu : cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T) ∈ Φ.source) :
    Tendsto (fun t => F t (Φ (cubicFlowCylinder σ a
      ((MorseHandle.splitCoordinates σ).symm u, T)))) atTop (𝓝 p) ↔ u.1 = 0 := by
  rw [hbasin _ hu]
  have he : (∀ i, σ i = -1 → (cubicFlowCylinder σ a
      ((MorseHandle.splitCoordinates σ).symm u, T)).2 i = 0) ↔
      ∀ i, σ i = -1 → (MorseHandle.splitCoordinates σ).symm u i = 0 := by
    simp only [cubicFlowCylinder_transverse_zero_iff]
  rw [he, ← TransverseGerms.splitCoordinates_negative_zero_iff]
  rw [(MorseHandle.splitCoordinates σ).apply_symm_apply]

open Classical in
theorem outgoing_cubic_slice_basin (σ : Fin m → ℝ)
    (hσ : ∀ i, σ i = -1 ∨ σ i = 1) (a T : ℝ)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (F : Flow ℝ M) {q : M}
    (hbasin : ∀ z ∈ Φ.source, Tendsto (fun t => F t (Φ z)) atBot (𝓝 q) ↔
      ∀ i, σ i = 1 → z.2 i = 0)
    (u : MorseHandle.NegativeSpace σ × MorseHandle.PositiveSpace σ)
    (hu : cubicFlowCylinder σ a ((MorseHandle.splitCoordinates σ).symm u, T) ∈ Φ.source) :
    Tendsto (fun t => F t (Φ (cubicFlowCylinder σ a
      ((MorseHandle.splitCoordinates σ).symm u, T)))) atBot (𝓝 q) ↔ u.2 = 0 := by
  rw [hbasin _ hu]
  have he : (∀ i, σ i = 1 → (cubicFlowCylinder σ a
      ((MorseHandle.splitCoordinates σ).symm u, T)).2 i = 0) ↔
      ∀ i, σ i = 1 → (MorseHandle.splitCoordinates σ).symm u i = 0 := by
    simp only [cubicFlowCylinder_transverse_zero_iff]
  rw [he, ← TransverseGerms.splitCoordinates_positive_zero_iff σ hσ]
  rw [(MorseHandle.splitCoordinates σ).apply_symm_apply]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
