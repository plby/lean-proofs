import Wikipedia.HopfProblem.DegreeCollapseAttachingCircleLowerTransport

/-!
# The transported attaching sphere is the entire backward-basin section

Every noncritical point in the backward basin crosses the actual attaching
level. Its parametrization there and uniqueness of a regular-level orbit
crossing identify the full transported section, not just a subset of it.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.backward_basin_reaches_attaching_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) {x : M} (hx : x ∉ criticalPoints E f)
    (hback : Tendsto (fun t => S.flow t x) atBot (𝓝 p.val)) :
    x ∈ FlowCancellation.levelBasin S.flow f (S.toSurgeryWindows.lower p) := by
  obtain ⟨r, hr, q, hq, hback', hforward, hheights⟩ := FlowCancellation.exists_native_descent_endpoints
    hf S.smooth S.flow S.integral S.zero S.descent S.distinct x
  have hrp : r = p.val := tendsto_nhds_unique hback' hback
  have hqp : f q < f p := by
    have hh := (hheights hx).1.trans (hheights hx).2
    rwa [hrp] at hh
  have hqlo : f q < S.toSurgeryWindows.lower p :=
    (S.toSurgeryWindows.value_lt_upper ⟨q, hq⟩).trans (S.separated ⟨q, hq⟩ p hqp)
  exact FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hback hforward (S.toSurgeryWindows.lower_lt_value p) hqlo

theorem AdaptedSurgeryWindows.transported_attaching_range_iff
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    {X : Type*} (e : X → sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (he : Surjective e) (Γ : X → {y : M // f y = a})
    (hflow : ∀ z, ∃ t : ℝ, S.flow t ((S.data p).surgery.attachingSphere (e z)).val = (Γ z).val)
    (y : {x : M // f x = a}) :
    y ∈ range Γ ↔ Tendsto (fun t => S.flow t y.val) atBot (𝓝 p.val) := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := hflow z
    have hback := (S.attaching_basin_iff hf p ((S.data p).surgery.attachingSphere (e z))).mpr
      ⟨e z, rfl⟩
    rw [← ht]
    exact (flow_time_atBot_limit_iff S.flow t _ p.val).mpr hback
  · intro hy
    obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf p (ha y.val y.property) hy
    let x : (S.data p).LowerLevel := ⟨S.flow t y.val, ht⟩
    have hxback : Tendsto (fun s => S.flow s x.val) atBot (𝓝 p.val) :=
      (flow_time_atBot_limit_iff S.flow t y.val p.val).mpr hy
    obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p x).mp hxback
    obtain ⟨z, hz⟩ := he u
    obtain ⟨s, hs⟩ := hflow z
    have hattach : S.flow t y.val = ((S.data p).surgery.attachingSphere (e z)).val := by
      rw [hz]
      exact (congrArg Subtype.val hu).symm
    have hshared : S.flow 0 (Γ z).val = S.flow (s + t) y.val := by
      rw [S.flow.map_zero_apply, S.flow.map_add, hattach, hs]
    refine ⟨z, Subtype.ext ?_⟩
    exact native_same_level_orbit_points hf S.smooth S.flow S.integral
      (fun w hw => S.descent w (ha w hw)) (Γ z).property y.property hshared

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
