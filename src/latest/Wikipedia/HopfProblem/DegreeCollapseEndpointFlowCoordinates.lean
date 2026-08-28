import Wikipedia.HopfProblem.DegreeCollapseNativeCubicSegments

/-!
# Constructed regular slices and exact flow formulas near cubic endpoints

Every neighborhood of a closed-axis point contains a full small regular
transverse slice. A native cubic endpoint chart then agrees with the actual
flow from that slice wherever the point and its transported transverse
coordinate stay in the constructed box. The radii and slice are constructed.
-/

noncomputable section

open Set Function Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {m : ℕ}

/-- Every axis-centered ball at a point of the closed cubic axis contains
a constructed regular transverse slice with positive uniform radius. -/
theorem exists_cubic_slice_in_axis_ball (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    {c r : ℝ} (hc : c ∈ Icc (-a) a) (hr : 0 < r) :
    ∃ (T δ : ℝ), 0 < δ ∧ ∀ z : Fin m → ℝ, ‖z‖ ≤ δ →
      cubicFlowCylinder σ a (z, T) ∈ ball (c, (0 : Fin m → ℝ)) r := by
  have hcl : c ∈ closure (Ioo (-a) a) := by
    rw [closure_Ioo (by linarith : -a ≠ a)]
    exact hc
  obtain ⟨s, hs, hdist⟩ := Metric.mem_closure_iff.mp hcl r hr
  let T := cubicAxisClock a s
  have hpoint : cubicFlowCylinder σ a (0, T) = (s, (0 : Fin m → ℝ)) := by
    rw [cubicFlowCylinder_axis]
    change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
    rw [cubicAxisParameter_clock ha hs]
  have hnear : cubicFlowCylinder σ a (0, T) ∈ ball (c, (0 : Fin m → ℝ)) r := by
    rw [hpoint, mem_ball, Prod.dist_eq, dist_self, max_eq_left (dist_nonneg : 0 ≤ dist s c)]
    simpa only [dist_comm] using hdist
  have hcont : Continuous (fun z : Fin m → ℝ => cubicFlowCylinder σ a (z, T)) :=
    (contDiff_cubicFlowCylinder σ a).continuous.comp (continuous_id.prodMk continuous_const)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hcont.continuousAt (isOpen_ball.mem_nhds hnear))
  refine ⟨T, δ, hδ, ?_⟩
  intro z hz
  exact hδsub (mem_closedBall_zero_iff.mpr hz)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Construct an endpoint-chart box and regular slice, then identify the
actual original flow formula throughout their regular overlap. -/
theorem exists_native_cubic_endpoint_flow_coordinates (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c : ℝ} (hc : c ∈ Icc (-a) a) (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source) :
    ∃ (r δ T : ℝ), 0 < r ∧ 0 < δ ∧
      closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source ∧
      (∀ z : Fin m → ℝ, ‖z‖ ≤ δ →
        cubicFlowCylinder σ a (z, T) ∈ ball (c, (0 : Fin m → ℝ)) r) ∧
      ∀ p ∈ closedBall (c, (0 : Fin m → ℝ)) r, p.1 ∈ Ioo (-a) a →
        ‖(cubicFlowCylinderInverse σ a p).1‖ ≤ δ →
        Φ p = F (cubicAxisClock a p.1 - T)
          (Φ (cubicFlowCylinder σ a ((cubicFlowCylinderInverse σ a p).1, T))) := by
  obtain ⟨r, hr, hbox⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds hcΦ)
  obtain ⟨T, δ, hδ, hslice⟩ := exists_cubic_slice_in_axis_ball σ ha hc hr
  refine ⟨r, δ, T, hr, hδ, hbox, hslice, ?_⟩
  intro p hp hpa hpδ
  let z := (cubicFlowCylinderInverse σ a p).1
  have hinit := ball_subset_closedBall (hslice z hpδ)
  have hpoint : cubicFlowCylinder σ a (z, cubicAxisClock a p.1) = p :=
    cubicFlowCylinder_right_inv σ ha hpa
  have hfinish : cubicFlowCylinder σ a (z, cubicAxisClock a p.1) ∈
      closedBall (c, (0 : Fin m → ℝ)) r := hpoint.symm ▸ hp
  have hh := native_cubic_flow_between_box_points σ ha Φ hV hmodel F hF hbox z hinit hfinish
  rw [hpoint] at hh
  exact hh.symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
