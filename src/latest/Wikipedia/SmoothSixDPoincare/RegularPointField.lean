import Wikipedia.SmoothSixDPoincare.ManifoldCriticalPoints
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# A smooth unit-speed ascent field near each regular point

A nonzero coordinate differential detects a constant direction. Pull it
back through the genuine chart and divide by its nonvanishing derivative
of the original function. The resulting native vector field satisfies
`df(V) = 1` on an open neighborhood of the regular point.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

def chartDirection (e : OpenPartialHomeomorph M E) (w : E) :
    (x : M) → TangentSpace 𝓘(ℝ, E) x :=
  VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) e
    (fun y => (NormedSpace.fromTangentSpace y).symm w)

/-- Pulling back a constant coordinate direction gives a smooth field on the chart source. -/
theorem contMDiffOn_chartDirection {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) (w : E) :
    ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, chartDirection e w x⟩ : TangentBundle 𝓘(ℝ, E) M)) e.source := by
  have hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun y : E => (⟨y, (NormedSpace.fromTangentSpace y).symm w⟩ :
        TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have he' : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  intro x hx
  have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x).IsInvertible :=
    ⟨he'.mfderiv hx, rfl⟩
  exact ((hW (e x)).mpullback_vectorField_preimage
    (contMDiffAt_of_mem_maximalAtlas he hx) hinv (by simp)).contMDiffWithinAt

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The derivative along the pulled-back direction is exactly the coordinate differential. -/
theorem mvfderiv_chartDirection {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (w : E) {x : M} (hx : x ∈ e.source) :
    mvfderiv 𝓘(ℝ, E) f x (chartDirection e w x) =
      fderiv ℝ (f ∘ e.symm) (e x) w := by
  have he' : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas he).mdifferentiableOn (by simp),
      (contMDiffOn_symm_of_mem_maximalAtlas he).mdifferentiableOn (by simp)⟩
  have h₁ := he'.comp_symm_deriv (e.map_source hx)
  rw [e.left_inv hx] at h₁
  have hi := ContinuousLinearMap.inverse_eq h₁ (he'.symm_comp_deriv hx)
  have hc : fderiv ℝ (f ∘ e.symm) (e x) =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp (e x)
      (hf.mdifferentiableAt (by simp)) (he'.mdifferentiableAt_symm (e.map_source hx))]
    rw [e.left_inv hx]
  unfold chartDirection
  rw [VectorField.mpullback_apply, hi]
  exact (congrArg (fun A : E →L[ℝ] ℝ => A w) hc).symm

/-- At a regular point there is a genuine local smooth field with derivative of `f` equal to one. -/
theorem exists_unitSpeedField_near_regular {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hp : p ∉ ManifoldMorse.criticalPoints E f) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
        ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) U ∧
        ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) f x (V x) = 1 := by
  classical
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hpS : p ∈ e.source := mem_chart_source E p
  have hdf : fderiv ℝ (f ∘ e.symm) (e p) ≠ 0 :=
    fun h => hp ((ManifoldMorse.mem_criticalPoints_iff hf he hpS).mpr h)
  have hw : ∃ w : E, fderiv ℝ (f ∘ e.symm) (e p) w ≠ 0 := by
    by_contra! h
    exact hdf (ContinuousLinearMap.ext h)
  obtain ⟨w, hw⟩ := hw
  let D : M → ℝ := fun x => fderiv ℝ (f ∘ e.symm) (e x) w
  have hder := (ManifoldMorse.contDiffOn_chartExpression hf he).fderiv_of_isOpen
    e.open_target (m := ∞) (by simp)
  have hD : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ D e.source :=
    (hder.clm_apply contDiffOn_const).contMDiffOn.comp
      (contMDiffOn_of_mem_maximalAtlas he) (fun _ hx => e.map_source hx)
  let U : Set M := e.source ∩ D ⁻¹' {0}ᶜ
  have hU : IsOpen U := hD.continuousOn.isOpen_inter_preimage e.open_source
    (isClosed_singleton (x := (0 : ℝ))).isOpen_compl
  let V : (x : M) → TangentSpace 𝓘(ℝ, E) x := fun x => (D x)⁻¹ • chartDirection e w x
  refine ⟨U, hU, ⟨hpS, hw⟩, V, ?_, ?_⟩
  · exact ((hD.mono inter_subset_left).inv₀ (fun _ hx => hx.2)).smul_section
      ((contMDiffOn_chartDirection he w).mono inter_subset_left)
  · intro x hx
    change mvfderiv 𝓘(ℝ, E) f x ((D x)⁻¹ • chartDirection e w x) = 1
    rw [map_smul, smul_eq_mul, mvfderiv_chartDirection hf he w hx.1]
    exact inv_mul_cancel₀ hx.2

end Wikipedia.SmoothSixDPoincare.FlowConstruction
