import Wikipedia.HopfProblem.DegreeCollapseEndpointSliceOnOrbit
import Wikipedia.HopfProblem.DegreeCollapseFlowShiftedFieldCharts
import Wikipedia.SmoothSixDPoincare.DescendingFlow

/-!
# Normalizing a constructed endpoint chart to the original orbit clock

The regular slice center is a proved time on the original orbit. Shift
the endpoint chart by the corresponding fixed flow time. Its critical
point, source and exact cubic field are retained, while its regular axis
now has exactly the original orbit's cubic-time parametrization throughout
the constructed endpoint box.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The actual endpoint chart can be synchronized with the original whole
orbit clock without modifying the field, its source, or its critical point. -/
theorem exists_clock_normalized_cubic_endpoint (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c : ℝ} (hc : c ∈ Icc (-a) a) (hcrit : c ^ 2 = a ^ 2)
    (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source)
    (x : M) {l : Filter ℝ} [NeBot l]
    (hlim : Tendsto (fun t => F t x) l (𝓝 (Φ (c, 0))))
    (htail : ∀ᶠ t in l, ∃ s ∈ Ioo (-a) a,
      (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∃ (Ψ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
      (r δ T : ℝ),
      Ψ.source = Φ.source ∧ Ψ (c, 0) = Φ (c, 0) ∧ 0 < r ∧ 0 < δ ∧
      closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source ∧
      (∀ z : Fin m → ℝ, ‖z‖ ≤ δ →
        cubicFlowCylinder σ a (z, T) ∈ ball (c, (0 : Fin m → ℝ)) r) ∧
      (∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y) ∧
      (∀ t : ℝ, cubicFlowCylinder σ a (0, t) ∈ closedBall (c, (0 : Fin m → ℝ)) r →
        Ψ (cubicFlowCylinder σ a (0, t)) = F t x) ∧
      ∃ d : ℝ, ∀ z : Model m, Ψ z = F d (Φ z) := by
  have hV₁ := hV.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)
  obtain ⟨r, δ, T, τ, hr, hδ, hbox, hslice, hcenter⟩ :=
    exists_endpoint_slice_on_actual_orbit σ ha Φ hV₁ hmodel F hF hc hcΦ x hlim htail
  have hs : ∀ t, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (F t) := fun t =>
    (SmoothODE.contMDiff_native_flow hV F hF).comp (contMDiff_id.prodMk contMDiff_const)
  let Ψ := Φ.trans (SmoothODE.nativeFlowTimeDiffeomorph F hs (T - τ)).toPartialDiffeomorph
  have hsource : Ψ.source = Φ.source := SmoothODE.flow_shifted_chart_source Φ F hs (T - τ)
  have hΨmodel : ∀ y ∈ Ψ.target, V y = nativeCubicDescent σ Ψ (-(a ^ 2)) y := by
    intro y hy
    exact SmoothODE.partialChartField_flow_shift Φ F hs hF (cubicDescent σ (-(a ^ 2)))
      hmodel (T - τ) hy
  have hzero : V (Φ (c, 0)) = 0 := by
    rw [hmodel _ (Φ.map_source' hcΦ)]
    have hinv : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hcΦ
    have hw : cubicDescent σ (-(a ^ 2)) (Φ.symm (Φ (c, 0))) = 0 := by
      rw [hinv]
      ext i <;> simp [cubicDescent, hcrit]
    unfold nativeCubicDescent FlowConstruction.partialChartField
    rw [VectorField.mpullback_apply, hw, map_zero, map_zero]
  have hvalue : Ψ (c, 0) = Φ (c, 0) :=
    FlowConstruction.flow_fixed_of_zero hV₁ F hF hzero (T - τ)
  have hΨbox : closedBall (c, (0 : Fin m → ℝ)) r ⊆ Ψ.source := hsource.symm ▸ hbox
  have hbase : Ψ (cubicFlowCylinder σ a (0, T)) = F T x := by
    change F (T - τ) (Φ (cubicFlowCylinder σ a (0, T))) = F T x
    rw [hcenter, ← F.map_add, sub_add_cancel]
  refine ⟨Ψ, r, δ, T, hsource, hvalue, hr, hδ, hΨbox, hslice, hΨmodel, ?_,
    T - τ, fun _ => rfl⟩
  intro t ht
  have hstart : cubicFlowCylinder σ a (0, T) ∈ closedBall (c, (0 : Fin m → ℝ)) r :=
    ball_subset_closedBall (hslice 0 (by simpa using hδ.le))
  have hh := native_cubic_flow_between_box_points σ ha Ψ hV₁ hΨmodel F hF hΨbox 0 hstart ht
  rw [hbase, ← F.map_add, sub_add_cancel] at hh
  exact hh.symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
