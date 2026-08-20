import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.PolygonalArcEndpointIsolationExists

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcTargetEndpointRayCover]
lemma PolygonalArcTargetEndpointRayCover (γ : PolygonalArc) :
    ∃ r : ℝ, 0 < r ∧
      (let hprev : γ.vertices.length - 2 < γ.vertices.length := by
        have hlen := γ.length_ge_two
        omega
       Metric.ball γ.target r ∩ γ.carrier ⊆
        {x | ∃ c : ℝ, 0 ≤ c ∧
          x = γ.target +
            c • (γ.vertices[γ.vertices.length - 2]'hprev - γ.target)}) := by
-- BODY
  obtain ⟨r₀, r₁, hIso⟩ := PolygonalArcEndpointIsolationExists γ
  refine ⟨r₁, hIso.target_pos, ?_⟩
  dsimp
  intro x hx
  have hxclosed : x ∈ Metric.closedBall γ.target r₁ := by
    exact Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hx.1))
  have hxseg := hIso.target_closedBall_carrier_subset_terminal_segment
    ⟨hxclosed, hx.2⟩
  rw [segment_eq_image_lineMap] at hxseg
  rcases hxseg with ⟨t, ht, htx⟩
  refine ⟨t, ht.1, ?_⟩
  rw [← htx]
  rw [AffineMap.lineMap_apply_module]
  module
