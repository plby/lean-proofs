import Wikipedia.HopfProblem.DegreeCollapseNativeModelFieldReplacement
import Wikipedia.HopfProblem.DegreeCollapseNativeCylinderInvariance

/-!
# Native integral curves transported through a genuine model manifold

The inverse differential identifies the native pullback field, so actual
integral curves on the regular-level product lift to original-manifold
integral curves. Uniqueness identifies the complete flows and proves
invariance of the actual cylinder target.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {D E H X M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
  {I : ModelWithCorners ℝ D H}
  [TopologicalSpace M] [ChartedSpace E M]

theorem native_model_pullback_eq_mfderiv_symm
    (e : PartialDiffeomorph 𝓘(ℝ, E) I M X ∞)
    (W : (z : X) → TangentSpace I z) {x : M} (hx : x ∈ e.source) :
    VectorField.mpullback 𝓘(ℝ, E) I e W x =
      mfderiv I 𝓘(ℝ, E) e.symm (e x) (W (e x)) := by
  let e' := e.toOpenPartialHomeomorph
  have he : e'.MDifferentiable 𝓘(ℝ, E) I :=
    ⟨e.contMDiffOn.mdifferentiableOn (by simp), e.symm.contMDiffOn.mdifferentiableOn (by simp)⟩
  have h₁ := he.comp_symm_deriv (e'.map_source hx)
  rw [e'.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he.symm_comp_deriv hx)
  rw [VectorField.mpullback_apply]
  change (mfderiv 𝓘(ℝ, E) I e' x).inverse (W (e' x)) = _
  rw [hi]
  rfl

theorem hasMFDerivAt_lift_native_model_curve
    (e : PartialDiffeomorph 𝓘(ℝ, E) I M X ∞)
    (W : (z : X) → TangentSpace I z) {α : ℝ → X} {t : ℝ}
    (hα : HasMFDerivAt 𝓘(ℝ, ℝ) I α t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (W (α t)))) (ht : α t ∈ e.target) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (e.symm ∘ α) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (VectorField.mpullback 𝓘(ℝ, E) I e W (e.symm (α t)))) := by
  have hi := (e.symm.contMDiffOn_toFun.contMDiffAt
    (e.open_target.mem_nhds ht)).mdifferentiableAt (by simp)
  have hd := hi.hasMFDerivAt.comp t hα
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  let s : ℝ := a
  change (mfderiv I 𝓘(ℝ, E) e.symm (α t)) (s • W (α t)) =
    s • VectorField.mpullback 𝓘(ℝ, E) I e W (e.symm (α t))
  rw [map_smul]
  have hp := native_model_pullback_eq_mfderiv_symm e W
    (x := e.symm (α t)) (e.map_target' ht)
  have hr : e (e.symm (α t)) = α t := e.right_inv' ht
  rw [hr] at hp
  exact congrArg (fun v : TangentSpace 𝓘(ℝ, E) (e.symm (α t)) => s • v) hp.symm

variable [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem native_model_flow_all_time
    (A : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V)
    (F : Flow ℝ X) (W : (z : X) → TangentSpace I z)
    (hF : ∀ p, IsMIntegralCurve (fun t => F t p) W)
    (hmodel : ∀ x ∈ A.target, V x = VectorField.mpullback 𝓘(ℝ, E) I A.symm W x)
    {p : X} (hstay : ∀ t, F t p ∈ A.source) :
    ∀ t, G t (A p) = A (F t p) := by
  let γ : ℝ → M := fun t => A (F t p)
  have hγ : IsMIntegralCurve γ V := by
    intro t
    have hd := hasMFDerivAt_lift_native_model_curve A.symm W (hF p t) (hstay t)
    have hd' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (VectorField.mpullback 𝓘(ℝ, E) I A.symm W (γ t))) := hd
    rw [← hmodel (γ t) (A.map_source' (hstay t))] at hd'
    exact hd'
  have heq := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless hV (hG (A p)) hγ
    (t₀ := 0) (by simp only [γ, G.map_zero_apply, F.map_zero_apply])
  exact fun t => congrFun heq t

theorem native_model_target_invariant
    (A : PartialDiffeomorph I 𝓘(ℝ, E) X M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (G : Flow ℝ M) (hG : ∀ x, IsMIntegralCurve (fun t => G t x) V)
    (F : Flow ℝ X) (W : (z : X) → TangentSpace I z)
    (hF : ∀ p, IsMIntegralCurve (fun t => F t p) W)
    (hmodel : ∀ x ∈ A.target, V x = VectorField.mpullback 𝓘(ℝ, E) I A.symm W x)
    (hstay : ∀ p ∈ A.source, ∀ t, F t p ∈ A.source) :
    ∀ x ∈ A.target, ∀ t, G t x ∈ A.target := by
  intro x hx t
  have hp := A.map_target' hx
  have heq := native_model_flow_all_time A hV G hG F W hF hmodel (hstay _ hp) t
  rw [A.right_inv' hx] at heq
  rw [heq]
  exact A.map_source' (hstay _ hp t)

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
