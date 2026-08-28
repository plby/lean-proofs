import Wikipedia.SmoothSixDPoincare.RegularPointField
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Vector fields pulled back through genuine partial diffeomorphisms

Unlike a fixed maximal-atlas chart, the coordinate target may have a
different normed model. This applies directly to the product Euclidean
Morse charts without replacing the manifold's original model or topology.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Pull an ordinary coordinate vector field back to the original tangent bundle. -/
def partialChartField
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) (W : F → F) :
    (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, F) e
    (fun y => (NormedSpace.fromTangentSpace y).symm (W y))

/-- Smoothness of the genuine pulled-back field on the source of the partial chart. -/
theorem contMDiffOn_partialChartField [CompleteSpace E] [IsManifold 𝓘(ℝ, E) ∞ M]
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) {W : F → F}
    (hW : ContDiff ℝ ∞ W) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, partialChartField e W x⟩ : TangentBundle 𝓘(ℝ, E) M)) e.source := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have hW' : ContMDiff 𝓘(ℝ, F) (𝓘(ℝ, F).tangent) ∞
      (fun y : F => (⟨y, (NormedSpace.fromTangentSpace y).symm (W y)⟩ :
        TangentBundle 𝓘(ℝ, F) F)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hW
  intro x hx
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x).IsInvertible := ⟨he.mfderiv hx, rfl⟩
  exact ((hW' (e x)).mpullback_vectorField_preimage
    ((e.contMDiffOn x hx).contMDiffAt (e.open_source.mem_nhds hx)) hinv (by simp)).contMDiffWithinAt

/-- Differentiation along the pulled-back field agrees with differentiation in coordinates. -/
theorem mvfderiv_partialChartField {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) M F ∞) (W : F → F)
    {x : M} (hx : x ∈ e.source) :
    mvfderiv 𝓘(ℝ, E) f x (partialChartField e W x) =
      fderiv ℝ (f ∘ e.symm) (e x) (W (e x)) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, F) :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₁ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he.symm_comp_deriv hx)
  have hc : fderiv ℝ (f ∘ e'.symm) (e' x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, E) e'.symm (e' x)) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp (e' x)
      (hf.mdifferentiableAt (by simp)) (he.mdifferentiableAt_symm (e'.map_source hx))]
    rw [e'.left_inv hx]
  unfold partialChartField
  rw [VectorField.mpullback_apply]
  change mvfderiv 𝓘(ℝ, E) f x
    ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e' x).inverse
      ((NormedSpace.fromTangentSpace (e' x)).symm (W (e' x)))) = _
  rw [hi]
  exact (congrArg (fun A : F →L[ℝ] ℝ => A (W (e' x))) hc).symm

end Wikipedia.SmoothSixDPoincare.FlowConstruction
