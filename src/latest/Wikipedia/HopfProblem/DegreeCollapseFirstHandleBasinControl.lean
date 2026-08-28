import Wikipedia.HopfProblem.DegreeCollapseSmoothCappedMeridian

/-!
# Every other point of the first handle's upper level crosses the original cut

The actual whole-belt complement has forward endpoint below the selected
critical value. Since that value is first above the original regular cut,
the endpoint lies below the cut. Thus the capped sphere's unique belt point
is its only point whose descending orbit does not cross the original cut.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.first_above_cut_upper_point_crosses_iff
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {c : ℝ} (hc : ∀ y, f y = c → y ∉ criticalPoints E f)
    (q : criticalPoints E f) (hcq : c < f q)
    (hfirst : ∀ p : criticalPoints E f, c < f p → f q ≤ f p)
    (x : (S.data q).UpperLevel) :
    x.val ∈ FlowCancellation.levelBasin S.flow f c ↔
      x ∉ range (S.data q).surgery.beltSphere := by
  constructor
  · rintro ⟨t, ht⟩ hx
    have hforward := (S.belt_basin_iff hf q x).mpr hx
    have hshift : Tendsto (fun s => S.flow s (S.flow t x.val)) atTop (𝓝 q.val) :=
      (flow_time_atTop_limit_iff S.flow t x.val q.val).mpr hforward
    have hbelow := S.forward_limit_below_regular_level hf hc ⟨S.flow t x.val, ht⟩ hshift
    exact hcq.not_gt hbelow
  · intro hx
    obtain ⟨a, _, b, hb, hback, hforward, hheights⟩ :=
      FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
        S.zero S.descent S.distinct x.val
    obtain ⟨t, ht⟩ := S.belt_complement_reaches_lower_level hf q x hx
    have hshift : Tendsto (fun s => S.flow s (S.flow t x.val)) atTop (𝓝 b) :=
      (flow_time_atTop_limit_iff S.flow t x.val b).mpr hforward
    have hbq : f b < f q :=
      (S.forward_limit_below_regular_level hf (S.data q).lower_regular
        ⟨S.flow t x.val, ht⟩ hshift).trans (S.toSurgeryWindows.lower_lt_value q)
    have hbc : f b < c := by
      have hle : f b ≤ c := le_of_not_gt (fun h => hbq.not_ge (hfirst ⟨b, hb⟩ h))
      exact lt_of_le_of_ne hle (fun h => hc b h hb)
    have hca : c < f a :=
      (hcq.trans ((S.toSurgeryWindows.value_lt_upper q).trans_eq x.property.symm)).trans
        (hheights ((S.data q).upper_regular x.val x.property)).2
    exact FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
      hback hforward hca hbc

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
