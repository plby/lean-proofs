import ErdosProblems.Erdos223.SphericalEuler.ComponentSum
import ErdosProblems.Erdos223.SphericalEuler.PlaneDrawing
import ErdosProblems.Erdos223.SphericalEuler.DrawingRestriction

open Set Schoenflies
open scoped Graph SimpleGraph

namespace SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance scratchComponentFintype (C : G.ConnectedComponent) : Fintype C :=
  Fintype.ofFinite C

noncomputable local instance scratchComponentAdjDecidable (C : G.ConnectedComponent) :
    DecidableRel C.toSimpleGraph.Adj := Classical.decRel _

def ConnectedComponent.neighborEquiv (C : G.ConnectedComponent) (u : C) :
    C.toSimpleGraph.neighborSet u ≃ G.neighborSet u.1 where
  toFun w := ⟨w.1.1, by
    have hw : C.toSimpleGraph.Adj u w.1 := w.2
    simpa [ConnectedComponent.toSimpleGraph] using hw⟩
  invFun w :=
    have hw : G.Adj u.1 w.1 := w.2
    ⟨⟨w.1, C.mem_supp_of_adj_mem_supp u.2 hw⟩,
      by simpa [ConnectedComponent.toSimpleGraph] using hw⟩
  left_inv w := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv w := by apply Subtype.ext; rfl

lemma ConnectedComponent.degree_toSimpleGraph_eq (C : G.ConnectedComponent) (u : C) :
    C.toSimpleGraph.degree u = G.degree u.1 := by
  rw [← C.toSimpleGraph.card_neighborSet_eq_degree,
    ← G.card_neighborSet_eq_degree]
  exact Fintype.card_congr (C.neighborEquiv G u)

lemma ConnectedComponent.minDegree_of_minDegree
    (C : G.ConnectedComponent) (hmin : ∀ v, 2 ≤ G.degree v) :
    ∀ u, 2 ≤ C.toSimpleGraph.degree u := by
  intro u
  rw [C.degree_toSimpleGraph_eq G u]
  exact hmin u

lemma ConnectedComponent.isBipartite (C : G.ConnectedComponent)
    (hbi : G.IsBipartite) : C.toSimpleGraph.IsBipartite :=
  hbi.of_hom C.toSimpleGraph_hom

/-- Component summation reduces an arbitrary crossing-free bipartite drawing
to the connected case. -/
theorem edge_add_four_le_of_connected_drawing_bound
    [Nonempty V]
    (pos : V → Plane) (drawing : Sym2 V → ℝ → Plane)
    (hpos : Function.Injective pos)
    (hdraw : Graph.IsDrawing ((Graph.ofSimpleGraph G).map pos) drawing)
    (hmin : ∀ v, 2 ≤ G.degree v) (hbi : G.IsBipartite)
    (hconnected : ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj]
      (p : W → Plane) (D : Sym2 W → ℝ → Plane),
      H.Connected → (∀ w, 2 ≤ H.degree w) → H.IsBipartite →
      Function.Injective p →
      Graph.IsDrawing ((Graph.ofSimpleGraph H).map p) D →
      H.edgeFinset.card + 4 ≤ 2 * Fintype.card W) :
    G.edgeFinset.card + 4 ≤ 2 * Fintype.card V := by
  apply G.edge_add_four_le_two_mul_card_of_connectedComponent
  intro C
  let f : C ↪ V := Function.Embedding.subtype C.supp
  have hgraph : G.comap f = C.toSimpleGraph := rfl
  have hdrawC := Graph.IsDrawing.comap f pos drawing hdraw
  rw [hgraph] at hdrawC
  exact hconnected C C.toSimpleGraph (pos ∘ f)
    (Graph.comapDrawing f drawing) C.connected_toSimpleGraph
    (C.minDegree_of_minDegree G hmin) (C.isBipartite G hbi)
    (hpos.comp f.injective) hdrawC

end SimpleGraph
