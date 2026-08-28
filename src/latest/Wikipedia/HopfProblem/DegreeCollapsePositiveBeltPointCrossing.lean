import Wikipedia.HopfProblem.DegreeCollapseBackwardObstructionAboveCut
import Wikipedia.HopfProblem.DegreeCollapseBeltPointUpperCrossing

/-!
# An actual belt point crossing the upper cut with only relative index bounds

The belt already lies strictly above the lower cut. Any backward endpoint
therefore also lies above it. Avoid the exact smooth family of backward
basins between the cuts and use the original flow endpoints to cross the
higher level. Critical points below the lower cut remain unrestricted.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_belt_point_reaching_level_above_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    {b a : ℝ} (hbq : b < f q) (hqa : f q < a) {d : ℕ}
    (hlow : ∀ p : criticalPoints E f, b < f p → f p ≤ a → nativeMorseIndex E f p ≤ d)
    (hdim : d < n) :
    ∃ v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
      ((S.data q).surgery.beltSphere v).val ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ := S.finite.fintype
  let K := BetweenBackwardBasinIndex S b a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := betweenBackwardBasinIndex_countable S b a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_between_backward_obstruction_images hf b a hlow
  let G : K × V → M := fun z => g z.1 z.2
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ G :=
    contMDiff_discrete_family g hg
  have hrange : range G = backwardBetweenBasins S b a := by
    rw [hcover]
    exact range_discrete_family g
  obtain ⟨v, hv⟩ := exists_belt_point_avoiding_smooth_image (S.data q) n G hG
    (show Module.finrank ℝ (Z × V) < n by
      simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim)
  let x := ((S.data q).surgery.beltSphere v).val
  have hforward := (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere v)).mpr ⟨v, rfl⟩
  obtain ⟨p, hp, _, _, hback, _, _⟩ := FlowCancellation.exists_native_descent_endpoints
    hf S.smooth S.flow S.integral S.zero S.descent S.distinct x
  have hxp : f x ≤ f p := by
    have hmono := FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    simpa only [S.flow.map_zero_apply] using
      hmono.ge_of_tendsto (hf.continuous.continuousAt.tendsto.comp hback) 0
  have hbx : b < f x := by
    change b < f ((S.data q).surgery.beltSphere v).val
    rw [((S.data q).surgery.beltSphere v).property]
    exact hbq.trans (S.toSurgeryWindows.value_lt_upper q)
  have hap : a < f p := lt_of_not_ge (fun h => hv (hrange.symm ▸
    (show x ∈ backwardBetweenBasins S b a from ⟨⟨p, hp⟩, hbx.trans_le hxp, h, hback⟩)))
  exact ⟨v, FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hback hforward hap hqa⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
