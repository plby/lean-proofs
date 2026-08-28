import Wikipedia.SmoothSixDPoincare.PartialChartVectorField
import Mathlib.Geometry.Manifold.IntegralCurve.Basic

/-!
# Lifting integral curves through genuine partial diffeomorphisms

The inverse-chart differential is the native pullback field. Consequently,
any coordinate solution in the chart target lifts to a native solution.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The pullback field is the inverse-chart differential on the chart source. -/
theorem partialChartField_eq_mfderiv_symm
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) (W : F → F)
    {x : M} (hx : x ∈ e.source) :
    partialChartField e W x = mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e.symm (e x)
      ((NormedSpace.fromTangentSpace (e x)).symm (W (e x))) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₁ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he.symm_comp_deriv hx)
  unfold partialChartField
  rw [VectorField.mpullback_apply]
  change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e' x).inverse
    ((NormedSpace.fromTangentSpace (e' x)).symm (W (e' x))) = _
  rw [hi]
  rfl

/-- A coordinate integral curve lifts to the actual pulled-back manifold field. -/
theorem hasMFDerivAt_lift_partialChartCurve
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) (W : F → F)
    {α : ℝ → F} {t : ℝ} (hα : HasDerivAt α (W (α t)) t) (ht : α t ∈ e.target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (e.symm ∘ α) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (partialChartField e W (e.symm (α t)))) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hi := (he.mdifferentiableAt_symm ht).hasMFDerivAt
  have hd := hi.comp t hα.hasFDerivAt.hasMFDerivAt
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e'.symm (α t))
    ((NormedSpace.fromTangentSpace t a) • (NormedSpace.fromTangentSpace (α t)).symm (W (α t))) =
      (NormedSpace.fromTangentSpace t a) • partialChartField e W (e'.symm (α t))
  rw [map_smul, partialChartField_eq_mfderiv_symm e W (e'.map_target ht)]
  rw [show e (e'.symm (α t)) = α t from e'.right_inv ht]
  rfl

end Wikipedia.SmoothSixDPoincare.FlowConstruction
