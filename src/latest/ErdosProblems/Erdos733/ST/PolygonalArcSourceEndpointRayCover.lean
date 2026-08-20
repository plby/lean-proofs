import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolationExists

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcSourceEndpointRayCover]
lemma PolygonalArcSourceEndpointRayCover (γ : PolygonalArc) :
    ∃ r : ℝ, 0 < r ∧
      (let hfirst : 1 < γ.vertices.length := Nat.lt_of_succ_le γ.length_ge_two
       Metric.ball γ.source r ∩ γ.carrier ⊆
        {x | ∃ c : ℝ, 0 ≤ c ∧
          x = γ.source + c • (γ.vertices[1]'hfirst - γ.source)}) := by
-- BODY
  obtain ⟨r₀, r₁, hIso⟩ := PolygonalArcEndpointIsolationExists γ
  refine ⟨r₀, hIso.source_pos, ?_⟩
  dsimp
  intro x hx
  have hxclosed : x ∈ Metric.closedBall γ.source r₀ := by
    exact Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx.1))
  have hxseg := hIso.source_closedBall_carrier_subset_initial_segment
    ⟨hxclosed, hx.2⟩
  rw [segment_eq_image_lineMap] at hxseg
  rcases hxseg with ⟨t, ht, htx⟩
  refine ⟨t, ht.1, ?_⟩
  rw [← htx]
  rw [AffineMap.lineMap_apply_module]
  module
