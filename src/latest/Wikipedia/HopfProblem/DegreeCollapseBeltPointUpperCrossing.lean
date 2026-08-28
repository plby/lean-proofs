import Wikipedia.HopfProblem.DegreeCollapseBeltPointImageAvoidance
import Wikipedia.HopfProblem.DegreeCollapseBackwardBasinObstacle
import Wikipedia.HopfProblem.DegreeCollapseDiscreteFamilySmooth

/-!
# A belt point whose reverse orbit reaches a prescribed higher level

The full low-backward obstruction has a countable smooth parametrization.
Its dimension is smaller than the belt's disk coordinates, so an actual
belt point avoids it. The original complete flow then crosses the higher
level between its genuine critical endpoints.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_belt_point_reaching_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = n + 1)]
    {a : ℝ} (hqa : f q < a) {d : ℕ}
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ d)
    (hdim : d < n) :
    ∃ v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
      ((S.data q).surgery.beltSphere v).val ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ := S.finite.fintype
  let K := LowBackwardBasinIndex S a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := lowBackwardBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_low_backward_obstruction_images hf a hlow
  let G : K × V → M := fun z => g z.1 z.2
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞ G :=
    contMDiff_discrete_family g hg
  have hrange : range G = backwardLowBasins S a := by
    rw [hcover]
    exact range_discrete_family g
  obtain ⟨v, hv⟩ := exists_belt_point_avoiding_smooth_image (S.data q) n G hG
    (show Module.finrank ℝ (Z × V) < n by
      simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim)
  have hforward := (S.belt_basin_iff hf q ((S.data q).surgery.beltSphere v)).mpr ⟨v, rfl⟩
  obtain ⟨p, hp, _, _, hback, _, _⟩ := FlowCancellation.exists_native_descent_endpoints
    hf S.smooth S.flow S.integral S.zero S.descent S.distinct
      ((S.data q).surgery.beltSphere v).val
  have hap : a < f p := lt_of_not_ge (fun h => hv (hrange.symm ▸
    (show ((S.data q).surgery.beltSphere v).val ∈ backwardLowBasins S a from
      ⟨⟨p, hp⟩, h, hback⟩)))
  exact ⟨v, FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hback hforward hap hqa⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
