import Mathlib.Combinatorics.SimpleGraph.Matching

/-! # Changing the ambient graph without changing a subgraph -/

namespace Erdos19

variable {V : Type*} {G H : SimpleGraph V}

def liftSubgraph (hHG : H ≤ G) (M : H.Subgraph) : G.Subgraph where
  verts := M.verts
  Adj := M.Adj
  adj_sub := fun h ↦ hHG h.adj_sub
  edge_vert := M.edge_vert
  symm := M.symm

@[simp] theorem liftSubgraph_verts (hHG : H ≤ G) (M : H.Subgraph) :
    (liftSubgraph hHG M).verts = M.verts := rfl

@[simp] theorem liftSubgraph_adj (hHG : H ≤ G) (M : H.Subgraph) (x y : V) :
    (liftSubgraph hHG M).Adj x y ↔ M.Adj x y := Iff.rfl

@[simp] theorem liftSubgraph_edgeSet (hHG : H ≤ G) (M : H.Subgraph) :
    (liftSubgraph hHG M).edgeSet = M.edgeSet := rfl

@[simp] theorem liftSubgraph_isMatching (hHG : H ≤ G) (M : H.Subgraph) :
    (liftSubgraph hHG M).IsMatching ↔ M.IsMatching := Iff.rfl

@[simp] theorem liftSubgraph_spanningCoe (hHG : H ≤ G) (M : H.Subgraph) :
    (liftSubgraph hHG M).spanningCoe = M.spanningCoe := rfl

end Erdos19
