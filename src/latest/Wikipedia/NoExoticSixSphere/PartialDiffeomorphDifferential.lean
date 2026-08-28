import Wikipedia.NoExoticSixSphere.ManifoldChartDerivative

/-!
# Continuous forward and inverse differentials of genuine Euclidean chart transitions

The linear equivalence is the actual derivative of the partial diffeomorphism.
Its inverse is the derivative of the actual inverse chart. Both vary
continuously throughout the original chart source.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ChartDifferential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (c : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞)

def differential (x : c.source) : E ≃L[ℝ] E :=
  (show IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c x.val from
    ⟨c, x.property, fun _ _ ↦ rfl⟩).mfderivToContinuousLinearEquiv (by simp)

theorem differential_toContinuousLinearMap (x : c.source) :
    (differential c x).toContinuousLinearMap = fderiv ℝ c x.val := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c x.val = fderiv ℝ c x.val
  exact mfderiv_eq_fderiv

theorem inverse_derivative_comp (x : c.source) :
    (fderiv ℝ c.symm (c x.val)).comp (fderiv ℝ c x.val) = ContinuousLinearMap.id ℝ E := by
  have hc : DifferentiableAt ℝ c x.val :=
    (c.contMDiffOn_toFun.contDiffOn.contDiffAt
      (c.open_source.mem_nhds x.property)).differentiableAt (by simp)
  have hi : DifferentiableAt ℝ c.symm (c x.val) :=
    (c.contMDiffOn_invFun.contDiffOn.contDiffAt
      (c.open_target.mem_nhds (c.map_source x.property))).differentiableAt (by simp)
  have he : (c.symm ∘ c) =ᶠ[𝓝 x.val] (id : E → E) := by
    filter_upwards [c.open_source.mem_nhds x.property] with y hy
    exact c.left_inv hy
  rw [← fderiv_comp x.val hi hc, he.fderiv_eq, fderiv_id]

theorem differential_symm_toContinuousLinearMap (x : c.source) :
    (differential c x).symm.toContinuousLinearMap = fderiv ℝ c.symm (c x.val) := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (differential c x).surjective v
  rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  have h := congrArg (fun L : E →L[ℝ] E ↦ L w) (inverse_derivative_comp c x)
  change w = (fderiv ℝ c.symm (c x.val)) ((differential c x).toContinuousLinearMap w)
  rw [differential_toContinuousLinearMap]
  exact h.symm

theorem continuous_differential : Continuous (fun x : c.source ↦
    (differential c x).toContinuousLinearMap) := by
  simp_rw [differential_toContinuousLinearMap]
  exact (c.contMDiffOn_toFun.contDiffOn.continuousOn_fderiv_of_isOpen
    c.open_source (by simp)).domRestrict

theorem continuous_inverse_differential : Continuous (fun x : c.source ↦
    (differential c x).symm.toContinuousLinearMap) := by
  simp_rw [differential_symm_toContinuousLinearMap]
  exact (c.contMDiffOn_invFun.contDiffOn.continuousOn_fderiv_of_isOpen
    c.open_target (by simp)).comp_continuous c.toOpenPartialHomeomorph.continuousOn.domRestrict
      (fun x ↦ c.map_source x.property)

end NoExoticSixSphere.ChartDifferential
