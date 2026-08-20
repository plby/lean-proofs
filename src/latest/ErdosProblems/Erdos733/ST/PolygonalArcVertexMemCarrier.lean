import ErdosProblems.Erdos733.ST.PolygonalArc

open Classical
noncomputable section

-- [TABLET NODE: PolygonalArcVertexMemCarrier]
lemma PolygonalArcVertexMemCarrier (Γ : PolygonalArc)
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ Γ.vertices) : p ∈ Γ.carrier := by
-- BODY
  rw [Γ.carrier_eq]
  rcases List.get_of_mem hp with ⟨k, hk⟩
  by_cases hnext : k.1 + 1 < Γ.vertices.length
  · refine ⟨k.1, hnext, ?_⟩
    rw [← hk]
    exact
      (left_mem_segment ℝ (Γ.vertices[k.1]) (Γ.vertices[k.1 + 1]))
  · have hkpos : 0 < k.1 := by
      by_contra hnot
      have hkzero : k.1 = 0 := Nat.eq_zero_of_not_pos hnot
      have : k.1 + 1 < Γ.vertices.length := by
        have hlen := Γ.length_ge_two
        omega
      exact hnext this
    let m := k.1 - 1
    have hm : m + 1 < Γ.vertices.length := by
      dsimp [m]
      rw [Nat.sub_add_cancel hkpos]
      exact k.2
    have hm_succ : m + 1 = k.1 := by
      dsimp [m]
      exact Nat.sub_add_cancel hkpos
    refine ⟨m, hm, ?_⟩
    rw [← hk]
    simpa [hm_succ] using
      (right_mem_segment ℝ (Γ.vertices[m]) (Γ.vertices[m + 1]))
