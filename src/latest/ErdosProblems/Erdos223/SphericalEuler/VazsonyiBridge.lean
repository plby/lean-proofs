import ErdosProblems.Erdos223.SphericalEuler.DrawingComponents
import ErdosProblems.Erdos223.SphericalEuler.DoubleCoverDegree
import ErdosProblems.Erdos223.SphericalEuler.SimpleGraphPlaneBound

open Metric Set Schoenflies
open scoped Graph SimpleGraph

namespace Erdos223.SphericalEuler

open GlobalDoubleCover

/-- The geometric double-cover construction reduces Vázsonyi's inequality to the
connected bipartite plane-graph inequality. -/
theorem diameterPairCount_add_two_le_of_connected_planar_bound
    (hconnected : ∀ (W : Type) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj]
      (p : W → Plane) (D : Sym2 W → ℝ → Plane),
      H.Connected → (∀ w, 2 ≤ H.degree w) → H.IsBipartite →
      Function.Injective p →
      Graph.IsDrawing ((Graph.ofSimpleGraph H).map p) D →
      H.edgeFinset.card + 4 ≤ 2 * Fintype.card W)
    (A : Finset (Point 3)) (hA : IsDiameterOne A)
    (hmin : ∀ v, 2 ≤ (diameterGraph A).degree v) :
    diameterPairCount A + 2 ≤ 2 * A.card := by
  classical
  obtain ⟨z, hz, havoid⟩ := exists_unit_not_mem_redBluePath_ranges hA hmin
  let V := {x // x ∈ A}
  let G := diameterGraph A
  let H := G.bipartiteDoubleCover
  have hV : Nonempty V := by
    obtain ⟨x, hx, -⟩ := hA.exists_dist_eq_one
    exact ⟨⟨x, hx⟩⟩
  letI : Nonempty V := hV
  have hH : Nonempty (V ⊕ V) := ⟨Sum.inl (Classical.choice hV)⟩
  letI : Nonempty (V ⊕ V) := hH
  have hdraw := isDrawing_planeDoubleCoverGraph hA hmin hz havoid
  have hbound := H.edge_add_four_le_of_connected_drawing_bound
    (planePos hA hmin z hz) (planeEdgeDrawing hA hmin hz havoid)
    (planePos_injective hA hmin hz havoid) hdraw
    (G.minDegree_bipartiteDoubleCover hmin)
    G.isBipartite_bipartiteDoubleCover hconnected
  rw [SimpleGraph.card_edgeFinset_bipartiteDoubleCover] at hbound
  simp only [Fintype.card_sum] at hbound
  change 2 * G.edgeFinset.card + 4 ≤
    2 * (Fintype.card V + Fintype.card V) at hbound
  have hcore : G.edgeFinset.card + 2 ≤ 2 * Fintype.card V := by omega
  simpa [diameterPairCount, G, V] using hcore

/-- Vázsonyi's inequality for a diameter-one configuration whose diameter graph has
minimum degree at least two.  The graph is drawn on a punctured sphere by the radial-fan
construction and counted using the connected bipartite plane-graph bound. -/
theorem diameterPairCount_add_two_le_of_minDegree_planar
    (A : Finset (Point 3)) (hA : IsDiameterOne A)
    (hmin : ∀ v, 2 ≤ (diameterGraph A).degree v) :
    diameterPairCount A + 2 ≤ 2 * A.card :=
  diameterPairCount_add_two_le_of_connected_planar_bound
    Graph.WeightedFaces.connectedSimpleGraphCallback A hA hmin

#print axioms diameterPairCount_add_two_le_of_minDegree_planar

end Erdos223.SphericalEuler
