import Wikipedia.HopfProblem.DegreeCollapseAttachingCircleBasinSection

/-!
# Attaching-branch endpoint control on the entire noncritical backward basin

Every noncritical backward-basin point crosses the actual attaching level.
The sphere section there and invariance along the complete flow transfer
the prescribed branch endpoint to the entire basin. This allows surgery
windows to shrink without losing their actual minimum branches.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.forward_endpoint_of_attaching_branches
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f)
    (hbranches : ∀ u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) atTop (𝓝 p.val))
    {x : M} (hx : x ∉ criticalPoints E f)
    (hback : Tendsto (fun t => S.flow t x) atBot (𝓝 q.val)) :
    Tendsto (fun t => S.flow t x) atTop (𝓝 p.val) := by
  obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf q hx hback
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Tendsto (fun s => S.flow s y.val) atBot (𝓝 q.val) :=
    (flow_time_atBot_limit_iff S.flow t x q.val).mpr hback
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf q y).mp hyback
  have hyforward : Tendsto (fun s => S.flow s y.val) atTop (𝓝 p.val) := by
    rw [← hu]
    exact hbranches u
  exact (flow_time_atTop_limit_iff S.flow t x p.val).mp hyforward

theorem AdaptedSurgeryWindows.attaching_branches_of_same_flow
    (S T : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hflow : T.flow = S.flow)
    (hbranches : ∀ u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) atTop (𝓝 p.val)) :
    ∀ u : sphere (0 : (T.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => T.flow t ((T.data q).surgery.attachingSphere u).val) atTop (𝓝 p.val) := by
  intro u
  let x := (T.data q).surgery.attachingSphere u
  have hback := (T.attaching_basin_iff hf q x).mpr ⟨u, rfl⟩
  rw [hflow] at hback ⊢
  exact S.forward_endpoint_of_attaching_branches hf p q hbranches
    ((T.data q).lower_regular x.val x.property) hback

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
