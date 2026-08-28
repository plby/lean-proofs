import Wikipedia.HopfProblem.DegreeCollapseSmoothIntegralCurve
import Wikipedia.SmoothSixDPoincare.MorseChartFlow

/-!
# Local flow comparison with a smooth scalar clock

A curve tangent to `e' • W` becomes an actual integral curve after the
inverse scalar coordinate change. Native ODE uniqueness then proves the
whole curve germ equals the complete flow with clock `e`.
-/

noncomputable section

open Set Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

/-- The derivatives of an actual scalar partial diffeomorphism and inverse multiply to one. -/
theorem scalar_chart_inverse_derivative
    (e : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞) {t : ℝ} (ht : t ∈ e.target) :
    deriv e (e.symm t) * deriv e.symm t = 1 := by
  have he : DifferentiableAt ℝ e (e.symm t) := (e.contMDiffOn_toFun.contDiffOn.contDiffAt
    (e.open_source.mem_nhds (e.map_target' ht))).differentiableAt (by simp)
  have hi : DifferentiableAt ℝ e.symm t := (e.symm.contMDiffOn_toFun.contDiffOn.contDiffAt
    (e.open_target.mem_nhds ht)).differentiableAt (by simp)
  have hright : (e ∘ e.symm) =ᶠ[𝓝 t] id := by
    filter_upwards [e.open_target.mem_nhds ht] with s hs
    exact e.right_inv' hs
  have h := hright.deriv_eq
  rw [deriv_comp t he hi, deriv_id] at h
  exact h

/-- A smooth scalar clock with nonzero derivative has an actual local inverse
inside any prescribed open neighborhood. -/
theorem exists_scalar_clock_chart {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {s : ℝ} (hd : deriv g s ≠ 0) {U : Set ℝ} (hU : IsOpen U) (hs : s ∈ U) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      s ∈ e.source ∧ e.source ⊆ U ∧ (e : ℝ → ℝ) = g := by
  have hder := (hg.differentiable (by simp) s).hasDerivAt.hasFDerivAt
  have hi : Function.Injective (fderiv ℝ g s) := by
    rw [hder.fderiv]
    intro x y hxy
    change x * deriv g s = y * deriv g s at hxy
    exact mul_right_cancel₀ hd hxy
  let A : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ g s).toLinearMap hi).toContinuousLinearEquiv
  exact NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn
    hU hs hg.contDiffOn ⟨A, rfl⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {W : (x : M) → TangentSpace 𝓘(ℝ, E) x} {α : ℝ → M}

/-- The inverse scalar clock turns the given native curve into a local integral curve. -/
theorem integralCurveAt_inverse_clock
    (e : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (hα : ∀ s ∈ e.source, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) α s
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((deriv e s) • W (α s))))
    {s₀ : ℝ} (hs₀ : s₀ ∈ e.source) :
    IsMIntegralCurveAt (α ∘ e.symm) W (e s₀) := by
  filter_upwards [e.open_target.mem_nhds (e.map_source' hs₀)] with t ht
  have hi : HasDerivAt e.symm (deriv e.symm t) t :=
    ((e.contMDiffOn_invFun.contDiffOn.contDiffAt
      (e.open_target.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt
  have hd := (hα (e.symm t) (e.map_target' ht)).comp t hi.hasFDerivAt.hasMFDerivAt
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ((NormedSpace.fromTangentSpace t r) * deriv e.symm t) •
    (deriv e (e.symm t) • W (α (e.symm t))) =
      (NormedSpace.fromTangentSpace t r) • W (α (e.symm t))
  rw [smul_smul, mul_assoc, mul_comm (deriv e.symm t), scalar_chart_inverse_derivative e ht,
    mul_one]

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Native uniqueness proves equality of full germs, rather than just equality at one point. -/
theorem eventually_eq_flow_with_clock
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) W)
    (e : PartialDiffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (hα : ∀ s ∈ e.source, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) α s
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((deriv e s) • W (α s))))
    {s₀ : ℝ} (hs₀ : s₀ ∈ e.source) :
    α =ᶠ[𝓝 s₀] (fun s => F (e s - e s₀) (α s₀)) := by
  let β := α ∘ e.symm
  let δ := fun t => F (t - e s₀) (α s₀)
  have hβ : IsMIntegralCurveAt β W (e s₀) := integralCurveAt_inverse_clock e hα hs₀
  have hδ : IsMIntegralCurve δ W := by
    simpa only [δ, sub_eq_add_neg, Function.comp_def] using (hcurve (α s₀)).comp_add (-e s₀)
  have hβ₀ : β (e s₀) = α s₀ := congrArg α (e.left_inv' hs₀)
  have hδ₀ : δ (e s₀) = α s₀ := by simp only [δ, sub_self, Flow.map_zero_apply]
  have heq : β =ᶠ[𝓝 (e s₀)] δ :=
    isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless hW.contMDiffAt hβ
      (hδ.isMIntegralCurveAt _) (hβ₀.trans hδ₀.symm)
  have he : ContinuousAt e s₀ := e.toOpenPartialHomeomorph.continuousAt hs₀
  filter_upwards [e.open_source.mem_nhds hs₀, heq.comp_tendsto he] with s hs heqs
  change α (e.symm (e s)) = F (e s - e s₀) (α s₀) at heqs
  exact (congrArg α (e.left_inv' hs)).symm.trans heqs

/-- The clock chart is constructed from the scalar height and its nonzero derivative;
only the genuine local tangent identity for the endpoint curve is required. -/
theorem eventually_eq_flow_with_scalar_height
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) W)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {s₀ : ℝ} (hd : deriv g s₀ ≠ 0)
    (hα : ∀ᶠ s in 𝓝 s₀, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) α s
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((deriv g s) • W (α s)))) :
    α =ᶠ[𝓝 s₀] (fun s => F (g s - g s₀) (α s₀)) := by
  obtain ⟨U, hUsub, hU, hs₀⟩ := mem_nhds_iff.mp hα
  obtain ⟨e, hs, hsource, he⟩ := exists_scalar_clock_chart hg hd hU hs₀
  have hαe : ∀ s ∈ e.source, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) α s
      ((1 : ℝ →L[ℝ] ℝ).smulRight ((deriv e s) • W (α s))) := by
    intro s hs
    rw [he]
    exact hUsub (hsource hs)
  simpa only [he] using eventually_eq_flow_with_clock hW F hcurve e hαe hs

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
