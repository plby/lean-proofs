import Wikipedia.SmoothSixDPoincare.SupportedPointMoving
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# Local point-moving diffeomorphisms inside an arbitrary open native set

Restrict an actual chart to the prescribed open set before using the
supported bump motion. Every sufficiently nearby point is reached by a
global diffeomorphism fixed on the entire complement of that open set.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] [T2Space M]

/-- Local transitivity is supplied by actual supported native diffeomorphisms. -/
theorem exists_open_pointMoving {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V,
      ∃ d : Diffeomorph J J M M ∞, d x = y ∧ ∀ z ∉ U, d z = z := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) x
  let Φ := PartialChart.restrictTarget c.symm hU
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c.symm (c x) = x := c.left_inv' hxc
  have hxΦ : c x ∈ Φ.source := by
    refine ⟨c.map_source' hxc, ?_⟩
    change c.symm (c x) ∈ U
    rw [hcx]
    exact hx
  have hΦx : Φ (c x) = x := hcx
  obtain ⟨ε, hε, hball, hmove⟩ := exists_supported_pointMoving Φ hxΦ
  refine ⟨Φ '' Metric.ball (c x) ε,
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball hball,
    ⟨c x, Metric.mem_ball_self hε, hΦx⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (Φ.map_source' (hball hv)).2
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨A, _, _, hdiff, hfix, hend⟩ := hmove v hv
    obtain ⟨d, hd⟩ := hdiff 1
    refine ⟨d, ?_, ?_⟩
    · rw [hΦx] at hend
      exact (hd x).symm.trans hend
    · intro z hz
      exact (hd z).symm.trans (hfix 1 z (fun h => hz h.2))

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
