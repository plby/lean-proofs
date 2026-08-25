import ErdosProblems.Erdos223.SphericalEuler.WeightedPlaneGraph
import Wikipedia.SchoenfliesTheorem.Graph.Redrawing

open Metric Set Schoenflies unitInterval
open scoped Graph

namespace Graph

variable {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}

namespace WeightedFaces

/-- A finite two-connected polygonal plane drawing admits the finite weighted face
decomposition constructed from a starting cycle by relative ears. -/
theorem nonempty_of_isTwoConnected [G.Finite]
    (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    (hG : G.IsTwoConnected) :
    Nonempty (WeightedFaces G drawing) := by
  have hnl : ∀ ⦃g x⦄, ¬ G.IsLoopAt g x := fun g x => h.not_isLoopAt g x
  obtain ⟨e, u, v, D, w, hcyc⟩ := hG.exists_long_cycle hnl
  refine hG.ear_decomposition
    (motive := fun B => Nonempty (WeightedFaces B drawing)) hnl
    hcyc.isTwoConnected hcyc.isCycle.cycleGraph_le
    ⟨ofCycle h hpoly hcyc.isCycle⟩ ?_
  intro B a b D' _ _ hBG hmot hpath hab ha hb hint
  obtain ⟨W⟩ := hmot
  rcases ear_edges_notMem_or_union_eq hBG hpath hab ha hb hint with hnew | heq
  · exact W.addEar h hpoly hBG hpath hab ha hb hint hnew
  · rw [heq]
    exact ⟨W⟩

#print axioms Graph.WeightedFaces.nonempty_of_isTwoConnected

/-- Sharp bipartite plane edge bound for a finite simple two-connected polygonal drawing. -/
theorem edge_add_four_le_two_vertices_of_polygonal_isDrawing
    [G.Finite] [G.Simple] (h : IsDrawing G drawing)
    (hpoly : ∀ g ∈ E(G), IsPolygonal (edgeArc drawing g))
    (hG : G.IsTwoConnected) (hbi : G.toSimpleGraph.IsBipartite) :
    E(G).ncard + 4 ≤ 2 * V(G).ncard := by
  obtain ⟨W⟩ := nonempty_of_isTwoConnected h hpoly hG
  exact W.edge_add_four_le_two_vertices_of_isBipartite hbi

#print axioms Graph.WeightedFaces.edge_add_four_le_two_vertices_of_polygonal_isDrawing

/-- Sharp bipartite plane edge bound for an arbitrary finite simple two-connected drawing;
polygonality is obtained by redrawing the same abstract graph. -/
theorem edge_add_four_le_two_vertices_of_isDrawing
    [G.Finite] [G.Simple] (h : IsDrawing G drawing)
    (hG : G.IsTwoConnected) (hbi : G.toSimpleGraph.IsBipartite) :
    E(G).ncard + 4 ≤ 2 * V(G).ncard := by
  obtain ⟨redrawing, hredrawing, hpoly⟩ := polygonal_redrawing G drawing h
  exact edge_add_four_le_two_vertices_of_polygonal_isDrawing
    hredrawing hpoly hG hbi

#print axioms Graph.WeightedFaces.edge_add_four_le_two_vertices_of_isDrawing

end WeightedFaces
end Graph
