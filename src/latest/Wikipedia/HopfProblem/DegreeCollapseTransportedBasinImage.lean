import Wikipedia.HopfProblem.DegreeCollapseNativeAttachingLowerCut

/-!
# Downward common-flow transport retains the entire backward basin image

A lower-level point with the specified higher backward endpoint must
cross the original source level. The source's full basin parametrization
and uniqueness on the target regular level then give surjectivity onto
the whole target basin, not only preservation of the labels of known points.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.transported_backward_basin_image
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : b < a) (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (p : M) (hap : a < f p)
    (α : X → {y : M // f y = a}) (β : X → {y : M // f y = b})
    (hα : ∀ x : {y : M // f y = a}, x ∈ range α ↔
      Tendsto (fun t => S.flow t x.val) atBot (𝓝 p))
    (horbit : ∀ z, ∃ t : ℝ, S.flow t (α z).val = (β z).val) :
    ∀ y : {x : M // f x = b}, y ∈ range β ↔
      Tendsto (fun t => S.flow t y.val) atBot (𝓝 p) := by
  intro y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := horbit z
    rw [← ht]
    exact (flow_time_atBot_limit_iff S.flow t (α z).val p).mpr
      ((hα (α z)).mp (mem_range_self z))
  · intro hy
    obtain ⟨q, hq, r, hr, _, hforward, hheights⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
        S.zero S.descent S.distinct y.val
    have hrb : f r < b := by
      simpa only [y.property] using (hheights (hb y.val y.property)).1
    obtain ⟨s, hs⟩ := FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
      hy hforward hap (hrb.trans hab)
    let x : {z : M // f z = a} := ⟨S.flow s y.val, hs⟩
    have hx : Tendsto (fun t => S.flow t x.val) atBot (𝓝 p) :=
      (flow_time_atBot_limit_iff S.flow s y.val p).mpr hy
    obtain ⟨z, hz⟩ := (hα x).mpr hx
    obtain ⟨t, ht⟩ := horbit z
    have hshared : S.flow 0 (β z).val = S.flow (t + s) y.val := by
      rw [S.flow.map_zero_apply, ← ht, hz]
      exact (S.flow.map_add t s y.val).symm
    refine ⟨z, Subtype.ext ?_⟩
    exact native_same_level_orbit_points hf S.smooth S.flow S.integral
      (fun z hz => S.descent z (hb z hz)) (β z).property y.property hshared

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
