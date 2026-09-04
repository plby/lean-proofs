import ErdosProblems.Erdos223.SphericalEuler.CutVertexSplit

open Metric Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

/-- A finite simple graph on at most two vertices has at most one edge. -/
theorem edge_ncard_le_one_of_vertex_ncard_le_two [G.Finite] [G.Simple]
    (hV : V(G).ncard ≤ 2) : E(G).ncard ≤ 1 := by
  classical
  by_cases hE : E(G).Nonempty
  · obtain ⟨e, he⟩ := hE
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
    have hpairsub : ({x, y} : Set Plane) ⊆ V(G) := by
      intro z hz
      rcases hz with rfl | rfl
      exacts [hxy.left_mem, hxy.right_mem]
    have hpaircard : ({x, y} : Set Plane).ncard = 2 := by
      simp [hxy.ne]
    have hpairs : ({x, y} : Set Plane) = V(G) := by
      apply Set.eq_of_subset_of_ncard_le hpairsub
      simpa [hpaircard] using hV
    have hEsub : E(G) ⊆ {e} := by
      intro f hf
      obtain ⟨p, q, hpq⟩ := exists_isLink_of_mem_edgeSet hf
      have hp : p = x ∨ p = y := by
        have := hpq.left_mem
        rw [← hpairs] at this
        simpa [eq_comm] using this
      have hq : q = x ∨ q = y := by
        have := hpq.right_mem
        rw [← hpairs] at this
        simpa [eq_comm] using this
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact (hpq.ne rfl).elim
      · simpa using (hxy.eq hpq).symm
      · simpa using (hxy.eq hpq.symm).symm
      · exact (hpq.ne rfl).elim
    exact (Set.ncard_le_ncard hEsub).trans_eq (by simp)
  · have hempty : E(G) = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
    simp [hempty]

#print axioms Graph.edge_ncard_le_one_of_vertex_ncard_le_two

namespace WeightedFaces

/-- The two-connected bound with a concrete bicoloring, used by cut-vertex induction. -/
theorem edge_add_four_le_two_vertices_of_isDrawing_isBicoloring
    [G.Finite] [G.Simple] (h : IsDrawing G drawing)
    (hG : G.IsTwoConnected) {c : Plane → Bool} (hc : G.IsBicoloring c) :
    E(G).ncard + 4 ≤ 2 * V(G).ncard := by
  obtain ⟨redrawing, hredrawing, hpoly⟩ := polygonal_redrawing G drawing h
  obtain ⟨W⟩ := nonempty_of_isTwoConnected hredrawing hpoly hG
  exact W.edge_add_four_le_two_vertices hc

#print axioms Graph.WeightedFaces.edge_add_four_le_two_vertices_of_isDrawing_isBicoloring

/-- The sharp bipartite plane edge bound for every finite simple connected plane graph with
at least three vertices.  The non-two-connected case splits at a cut vertex and recurses on
the two strictly smaller connected induced pieces. -/
theorem edge_add_four_le_two_vertices_of_connected_isDrawing_isBicoloring
    (G : Graph Plane β) [G.Finite] [G.Simple] (drawing : β → ℝ → Plane)
    (h : IsDrawing G drawing)
    (hconn : G.Connected) (hV : 3 ≤ V(G).ncard)
    {c : Plane → Bool} (hc : G.IsBicoloring c) :
    E(G).ncard + 4 ≤ 2 * V(G).ncard := by
  by_cases htwo : G.IsTwoConnected
  · exact edge_add_four_le_two_vertices_of_isDrawing_isBicoloring h htwo hc
  · have hthree : G.HasThreeVertices :=
      (hasThreeVertices_iff_ncard (finite_vertexSet G)).2 hV
    have hcut : ∃ v, G.IsCutVertex v := by
      by_contra hn
      push Not at hn
      have hdel : ∀ ⦃x⦄, x ∈ V(G) → (G.deleteVerts {x}).Connected := by
        intro x hx
        by_contra hnc
        exact hn x ⟨hx, hnc⟩
      exact htwo ⟨hthree, hconn, hdel⟩
    obtain ⟨v, hv⟩ := hcut
    obtain ⟨C⟩ := hv.exists_cutSplit hconn hthree
    let : C.A.Finite := Finite.of_le C.A_le
    let : C.B.Finite := Finite.of_le C.B_le
    let : C.A.Simple := Graph.Simple.anti C.A_le
    let : C.B.Simple := Graph.Simple.anti C.B_le
    have hdrawA : IsDrawing C.A drawing := h.mono C.A_le
    have hdrawB : IsDrawing C.B drawing := h.mono C.B_le
    have hcA : C.A.IsBicoloring c := by
      intro e u v hlink
      exact hc (hlink.mono C.A_le)
    have hcB : C.B.IsBicoloring c := by
      intro e u v hlink
      exact hc (hlink.mono C.B_le)
    have hboundA : E(C.A).ncard + 3 ≤ 2 * V(C.A).ncard := by
      by_cases hA3 : 3 ≤ V(C.A).ncard
      · have hrec := edge_add_four_le_two_vertices_of_connected_isDrawing_isBicoloring
          C.A drawing hdrawA C.A_connected hA3 hcA
        omega
      · have hAle : V(C.A).ncard ≤ 2 := by omega
        have hAe := edge_ncard_le_one_of_vertex_ncard_le_two (G := C.A) hAle
        have hA2 := C.two_le_A
        omega
    have hboundB : E(C.B).ncard + 3 ≤ 2 * V(C.B).ncard := by
      by_cases hB3 : 3 ≤ V(C.B).ncard
      · have hrec := edge_add_four_le_two_vertices_of_connected_isDrawing_isBicoloring
          C.B drawing hdrawB C.B_connected hB3 hcB
        omega
      · have hBle : V(C.B).ncard ≤ 2 := by omega
        have hBe := edge_ncard_le_one_of_vertex_ncard_le_two (G := C.B) hBle
        have hB2 := C.two_le_B
        omega
    have hVc := C.vertex_card_add
    have hEc := C.edge_card_add
    omega
termination_by V(G).ncard
decreasing_by
  · exact C.A_card_lt
  · exact C.B_card_lt

#print axioms Graph.WeightedFaces.edge_add_four_le_two_vertices_of_connected_isDrawing_isBicoloring

/-- Bipartite-facing form of the connected plane edge bound. -/
theorem edge_add_four_le_two_vertices_of_connected_isDrawing
    [G.Finite] [G.Simple] (h : IsDrawing G drawing)
    (hconn : G.Connected) (hV : 3 ≤ V(G).ncard)
    (hbi : G.toSimpleGraph.IsBipartite) :
    E(G).ncard + 4 ≤ 2 * V(G).ncard := by
  obtain ⟨c, hc⟩ := exists_isBicoloring_of_toSimpleGraph_isBipartite hbi
  exact edge_add_four_le_two_vertices_of_connected_isDrawing_isBicoloring
    G drawing h hconn hV hc

#print axioms Graph.WeightedFaces.edge_add_four_le_two_vertices_of_connected_isDrawing

end WeightedFaces
end Graph
