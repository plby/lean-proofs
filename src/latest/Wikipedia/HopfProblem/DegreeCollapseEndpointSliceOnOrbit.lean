import Wikipedia.HopfProblem.DegreeCollapseEndpointFlowCoordinates

/-!
# A constructed endpoint transverse slice centered on the actual orbit

The actual endpoint limit and the already proved far-tail axis membership
place a genuine orbit point inside the endpoint chart box. Native cubic
flow comparison then identifies the center of the constructed regular
slice with a specific time on that same original orbit.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] [T2Space M]
  {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- The endpoint chart constructs a regular transverse slice whose center
is proved to lie on the original selected complete orbit. -/
theorem exists_endpoint_slice_on_actual_orbit (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
    (Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) 1
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hmodel : ∀ y ∈ Φ.target, V y = nativeCubicDescent σ Φ (-(a ^ 2)) y)
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    {c : ℝ} (hc : c ∈ Icc (-a) a) (hcΦ : (c, (0 : Fin m → ℝ)) ∈ Φ.source)
    (x : M) {l : Filter ℝ} [NeBot l]
    (hlim : Tendsto (fun t => F t x) l (𝓝 (Φ (c, 0))))
    (htail : ∀ᶠ t in l, ∃ s ∈ Ioo (-a) a,
      (s, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (s, 0) = F t x) :
    ∃ (r δ T τ : ℝ), 0 < r ∧ 0 < δ ∧
      closedBall (c, (0 : Fin m → ℝ)) r ⊆ Φ.source ∧
      (∀ z : Fin m → ℝ, ‖z‖ ≤ δ →
        cubicFlowCylinder σ a (z, T) ∈ ball (c, (0 : Fin m → ℝ)) r) ∧
      Φ (cubicFlowCylinder σ a (0, T)) = F τ x := by
  obtain ⟨r, δ, T, hr, hδ, hbox, hslice, _⟩ :=
    exists_native_cubic_endpoint_flow_coordinates σ ha Φ hV hmodel F hF hc hcΦ
  have hcont := Φ.toOpenPartialHomeomorph.symm.continuousAt (Φ.map_source' hcΦ)
  have hcoord : Tendsto (fun t => Φ.symm (F t x)) l (𝓝 (c, (0 : Fin m → ℝ))) := by
    have hh : Tendsto (fun t => Φ.symm (F t x)) l (𝓝 (Φ.symm (Φ (c, 0)))) :=
      hcont.tendsto.comp hlim
    have hinv : Φ.symm (Φ (c, (0 : Fin m → ℝ))) = (c, 0) := Φ.left_inv' hcΦ
    rwa [hinv] at hh
  have hnear : ∀ᶠ t in l, Φ.symm (F t x) ∈ ball (c, (0 : Fin m → ℝ)) r :=
    hcoord.eventually (ball_mem_nhds _ hr)
  obtain ⟨t, htnear, s, hs, hsΦ, hsorbit⟩ := (hnear.and htail).exists
  have hinv : Φ.symm (F t x) = (s, (0 : Fin m → ℝ)) := by
    rw [← hsorbit]
    exact Φ.left_inv' hsΦ
  rw [hinv] at htnear
  have hpoint : cubicFlowCylinder σ a (0, cubicAxisClock a s) = (s, (0 : Fin m → ℝ)) := by
    rw [cubicFlowCylinder_axis]
    change (cubicAxisParameter a (cubicAxisClock a s), 0) = (s, 0)
    rw [cubicAxisParameter_clock ha hs]
  have hstart : cubicFlowCylinder σ a (0, cubicAxisClock a s) ∈
      closedBall (c, (0 : Fin m → ℝ)) r := hpoint.symm ▸ ball_subset_closedBall htnear
  have hfinish : cubicFlowCylinder σ a (0, T) ∈ closedBall (c, (0 : Fin m → ℝ)) r :=
    ball_subset_closedBall (hslice 0 (by simpa using hδ.le))
  have hflow := native_cubic_flow_between_box_points σ ha Φ hV hmodel F hF hbox 0 hstart hfinish
  rw [hpoint, hsorbit, ← F.map_add] at hflow
  exact ⟨r, δ, T, T - cubicAxisClock a s + t, hr, hδ, hbox, hslice, hflow.symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
