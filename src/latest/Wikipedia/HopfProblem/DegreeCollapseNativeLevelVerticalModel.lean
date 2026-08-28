import Wikipedia.HopfProblem.DegreeCollapseNativeModelCurveTransport
import Wikipedia.HopfProblem.DegreeCollapseNativeSuspensionCurves
import Wikipedia.HopfProblem.DegreeCollapseNativeFlowCylinder

/-!
# The original field in its genuine regular-level cylinder

Differentiating the actual original-flow formula proves that the field
is the native vertical pullback. The full regular-level cylinder is
therefore constructed with its field identity, not just as a smooth map.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z E N M : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace N] [ChartedSpace Z N] [IsManifold 𝓘(ℝ, Z) ∞ N]
  [TopologicalSpace M] [ChartedSpace E M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem native_level_flow_chart_vertical
    (A : PartialDiffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) (N × ℝ) M ∞)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (ι : N → M) (hformula : ∀ p : N × ℝ, A p = F p.2 (ι p.1)) :
    ∀ x ∈ A.target, V x = VectorField.mpullback 𝓘(ℝ, E)
      (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm nativeVerticalField x := by
  intro x hx
  let p := A.symm x
  have hp : p ∈ A.source := A.map_target' hx
  let α : ℝ → N × ℝ := fun t => (p.1, t)
  have hα : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) α p.2
      ((1 : ℝ →L[ℝ] ℝ).smulRight (nativeVerticalField (α p.2))) := by
    have hn : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) (fun _ : ℝ => p.1) p.2
        (0 : ℝ →L[ℝ] Z) := hasMFDerivAt_const p.1 p.2
    apply (hn.prodMk (hasMFDerivAt_id (I := 𝓘(ℝ, ℝ)) p.2)).congr_mfderiv
    apply ContinuousLinearMap.ext
    intro r
    let u : ℝ := r
    change ((0 : Z), u) = u • ((0 : Z), (1 : ℝ))
    simp
  have hd := hasMFDerivAt_lift_native_model_curve A.symm nativeVerticalField hα hp
  have heq : A.symm.symm ∘ α = fun t => F t (ι p.1) :=
    funext (fun t => hformula (p.1, t))
  rw [heq] at hd
  change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => F t (ι p.1)) p.2
    ((1 : ℝ →L[ℝ] ℝ).smulRight
      (VectorField.mpullback 𝓘(ℝ, E) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
        A.symm nativeVerticalField (A p))) at hd
  rw [hformula p] at hd
  have hpF : F p.2 (ι p.1) = x := (hformula p).symm.trans (A.right_inv' hx)
  have hh := (hcurve (ι p.1) p.2).mfderiv.symm.trans hd.mfderiv
  have hv := congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (F p.2 (ι p.1)) =>
    L (1 : ℝ)) hh
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at hv
  change V (F p.2 (ι p.1)) = VectorField.mpullback 𝓘(ℝ, E)
    (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) A.symm nativeVerticalField (F p.2 (ι p.1)) at hv
  rw [hpF] at hv
  exact hv

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

theorem exists_native_level_flow_cylinder_with_field {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hreg : ∀ x, f x = c → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (z : {x : M // f x = c}) :
    letI := RegularLevel.chartedSpace hf hreg
    ∃ A : PartialDiffeomorph (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        ({x : M // f x = c} × ℝ) M ∞,
      A.source = univ ∧ A.target = FlowCancellation.levelBasin F f c ∧
      (∀ p, A p = F p.2 p.1) ∧
      ∀ x ∈ A.target, V x = VectorField.mpullback 𝓘(ℝ, E)
        (𝓘(ℝ, RegularLevel.Model E).prod 𝓘(ℝ, ℝ)) A.symm nativeVerticalField x := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  obtain ⟨A, hsource, htarget, hformula, -⟩ :=
    FlowCancellation.exists_native_level_flow_cylinder hf hreg hV F hcurve hboundary z
  exact ⟨A, hsource, htarget, hformula,
    native_level_flow_chart_vertical A F hcurve Subtype.val hformula⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
