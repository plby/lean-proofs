import Wikipedia.HopfProblem.DegreeCollapseNativeFlowCylinder
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphProduct
import Wikipedia.SmoothSixDPoincare.PartialChartIntegralCurve
import Wikipedia.SmoothSixDPoincare.CenteredParametrization

/-!
# Euclidean flow cylinders with the actual vertical field

A genuine chart on the original regular level gives a Euclidean cylinder
over that chart for all real times. Native differentiation of the actual
flow proves that the original field is precisely the vertical coordinate
field, not merely tangent to the same trajectories.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {D E M : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- An exact flow-coordinate formula identifies the native field with vertical speed one. -/
theorem native_flow_chart_vertical
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × ℝ) 𝓘(ℝ, E) (D × ℝ) M ∞)
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (ι : D → M) (hformula : ∀ p : D × ℝ, Φ p = F p.2 (ι p.1)) :
    ∀ x ∈ Φ.target, V x = FlowConstruction.partialChartField Φ.symm (fun _ => (0, 1)) x := by
  intro x hx
  let p := Φ.symm x
  have hp : p ∈ Φ.source := Φ.map_target' hx
  let α : ℝ → D × ℝ := fun t => (p.1, t)
  have hα : HasDerivAt α ((0 : D), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hd := FlowConstruction.hasMFDerivAt_lift_partialChartCurve Φ.symm
    (fun _ : D × ℝ => (0, 1)) hα hp
  have heq : Φ.symm.symm ∘ α = fun t => F t (ι p.1) := funext (fun t => hformula (p.1, t))
  rw [heq] at hd
  change HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t => F t (ι p.1)) p.2
    ((1 : ℝ →L[ℝ] ℝ).smulRight
      (FlowConstruction.partialChartField Φ.symm (fun _ : D × ℝ => (0, 1)) (Φ p))) at hd
  rw [hformula p] at hd
  have hpF : F p.2 (ι p.1) = x := (hformula p).symm.trans (Φ.right_inv' hx)
  have hh := (hcurve (ι p.1) p.2).mfderiv.symm.trans hd.mfderiv
  have hv := congrArg (fun L : ℝ →L[ℝ] TangentSpace 𝓘(ℝ, E) (F p.2 (ι p.1)) =>
    L (1 : ℝ)) hh
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] at hv
  change V (F p.2 (ι p.1)) =
    FlowConstruction.partialChartField Φ.symm (fun _ : D × ℝ => (0, 1)) (F p.2 (ι p.1)) at hv
  rw [hpF] at hv
  exact hv

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]

/-- The original regular level and native flow construct an actual Euclidean
cylinder containing the entire selected orbit, with the exact old field. -/
theorem exists_euclidean_level_flow_cylinder {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hreg : ∀ x, f x = c → x ∉ ManifoldMorse.criticalPoints E f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hcurve : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hboundary : ∀ x, f x = c → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    {x : M} (hx : f x = c) :
    ∃ (U : Set (RegularLevel.Model E)) (ι : RegularLevel.Model E → M)
      (Φ : PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E × ℝ) 𝓘(ℝ, E)
        (RegularLevel.Model E × ℝ) M ∞),
      IsOpen U ∧ (0 : RegularLevel.Model E) ∈ U ∧ ι 0 = x ∧ Φ.source = U ×ˢ univ ∧
      (∀ y ∈ U, f (ι y) = c) ∧ (∀ p, Φ p = F p.2 (ι p.1)) ∧
      ∀ y ∈ Φ.target, V y = FlowConstruction.partialChartField Φ.symm (fun _ => (0, 1)) y := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let z : {x : M // f x = c} := ⟨x, hx⟩
  obtain ⟨C, hCsource, -, hCformula, -⟩ :=
    exists_native_level_flow_cylinder hf hreg hV F hcurve hboundary z
  let Q := NativeParametrization.centered (D := RegularLevel.Model E) z
  have hz : (0 : RegularLevel.Model E) ∈ Q.source :=
    NativeParametrization.zero_mem_centered_source z
  let A := PartialChart.prod Q (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph
  let P := (PartialChart.vectorProduct (RegularLevel.Model E) ℝ).toPartialDiffeomorph
  let Φ := (P.trans A).trans C
  let ι : RegularLevel.Model E → M := fun y => Q y
  have hsource : Φ.source = Q.source ×ˢ univ := by
    ext p
    change (p ∈ univ ∧ (p.1 ∈ Q.source ∧ p.2 ∈ univ)) ∧ A (P p) ∈ C.source ↔ _
    rw [hCsource]
    simp only [mem_univ, true_and, and_true, mem_prod]
  have hformula (p : RegularLevel.Model E × ℝ) : Φ p = F p.2 (ι p.1) :=
    hCformula (A (P p))
  refine ⟨Q.source, ι, Φ, Q.open_source, hz, ?_, hsource,
    fun y _ => (Q y).property, hformula, native_flow_chart_vertical Φ F hcurve ι hformula⟩
  exact congrArg Subtype.val (NativeParametrization.centered_zero z)

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
