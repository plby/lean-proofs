import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve
import ErdosProblems.Erdos733.ST.FinitePolygonalSet

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicListedPointOnElementarySegment]
lemma FinitePolygonalSetCyclicListedPointOnElementarySegment
    (J : SimpleClosedPolygonalCurve) (K : FinitePolygonalSet)
    (hKJ : K.carrier = J.carrier)
    (p : {p : EuclideanSpace ℝ (Fin 2) // p ∈ K.points}) :
    ∃ γ : {γ : PolygonalArc // γ ∈ J.edgeArcs},
      ∃ n : ℕ, ∃ hn : n + 1 < γ.1.vertices.length,
        p.1 ∈ segment ℝ
          (γ.1.vertices[n]'(Nat.lt_of_succ_lt hn))
          (γ.1.vertices[n + 1]'hn) := by
-- BODY
  have hpK : p.1 ∈ K.carrier := by
    rw [K.carrier_eq]
    exact Or.inl p.2
  have hpJ : p.1 ∈ J.carrier := by
    simpa [hKJ] using hpK
  rw [J.carrier_eq] at hpJ
  rcases Set.mem_iUnion.mp hpJ with ⟨γ, hpγ⟩
  rw [γ.1.carrier_eq] at hpγ
  rcases hpγ with ⟨n, hn, hpseg⟩
  exact ⟨γ, n, hn, by simpa using hpseg⟩
