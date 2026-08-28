import Wikipedia.HopfProblem.DegreeCollapseNormalizedEndpointClock

/-!
# Exact endpoint basins survive clock normalization

A fixed shift along the same complete flow changes neither endpoint
limit. Thus synchronizing the actual endpoint chart with the reference
orbit retains its stable and unstable basin descriptions everywhere.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {M : Type*} [TopologicalSpace M]

theorem flow_time_atTop_limit_iff (F : Flow ℝ M) (d : ℝ) (x p : M) :
    Tendsto (fun t => F t (F d x)) atTop (𝓝 p) ↔
      Tendsto (fun t => F t x) atTop (𝓝 p) := by
  have hshift {x p : M} (d : ℝ)
      (h : Tendsto (fun t => F t x) atTop (𝓝 p)) :
      Tendsto (fun t => F t (F d x)) atTop (𝓝 p) := by
    simpa only [comp_def, id_eq, F.map_add] using
      h.comp (tendsto_atTop_add_const_right atTop d tendsto_id)
  constructor
  · intro h
    simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hshift (-d) h
  · exact hshift d

theorem flow_time_atBot_limit_iff (F : Flow ℝ M) (d : ℝ) (x p : M) :
    Tendsto (fun t => F t (F d x)) atBot (𝓝 p) ↔
      Tendsto (fun t => F t x) atBot (𝓝 p) := by
  have hshift {x p : M} (d : ℝ)
      (h : Tendsto (fun t => F t x) atBot (𝓝 p)) :
      Tendsto (fun t => F t (F d x)) atBot (𝓝 p) := by
    simpa only [comp_def, id_eq, F.map_add] using
      h.comp (tendsto_atBot_add_const_right atBot d tendsto_id)
  constructor
  · intro h
    simpa only [← F.map_add, neg_add_cancel, F.map_zero_apply] using hshift (-d) h
  · exact hshift d

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {m : ℕ} {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- Normalize the actual endpoint clock and retain both endpoint basins,
with no separate compatibility premise on the original Morse coordinates. -/
theorem exists_basin_preserving_endpoint_clock (σ : Fin m → ℝ) {a : ℝ} (ha : 0 < a)
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
      ∀ z : Model m, ∀ p : M,
        (Tendsto (fun t => F t (Ψ z)) atTop (𝓝 p) ↔
          Tendsto (fun t => F t (Φ z)) atTop (𝓝 p)) ∧
        (Tendsto (fun t => F t (Ψ z)) atBot (𝓝 p) ↔
          Tendsto (fun t => F t (Φ z)) atBot (𝓝 p)) := by
  obtain ⟨Ψ, r, δ, T, hsource, hcenter, hr, hδ, hbox, hslice, hfield, haxis, d, hmap⟩ :=
    exists_clock_normalized_cubic_endpoint σ ha Φ hV hmodel F hF hc hcrit hcΦ x hlim htail
  refine ⟨Ψ, r, δ, T, hsource, hcenter, hr, hδ, hbox, hslice, hfield, haxis, ?_⟩
  intro z p
  rw [hmap]
  exact ⟨flow_time_atTop_limit_iff F d (Φ z) p, flow_time_atBot_limit_iff F d (Φ z) p⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
