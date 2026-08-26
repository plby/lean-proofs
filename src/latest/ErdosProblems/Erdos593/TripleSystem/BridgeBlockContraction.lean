import ErdosProblems.Erdos593.Graph.BridgeQuotient
import ErdosProblems.Erdos593.TripleSystem.BridgeBlocks

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Contracting bridge-free Levi components

Component-local infrastructure for the reverse structural direction.  A
degree-two hyperedge-node in a component of the bridge-free Levi graph is
contracted to an ordinary edge between its two point-neighbours.
-/

namespace Erdos593

open scoped Sym2

universe u v

namespace TripleSystem

variable {V : Type u} {E : Type v} (F : TripleSystem V E)

namespace BridgeBlock

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableRel F.levi.Adj]

/-- A connected component after all Levi bridges have been deleted. -/
abbrev Component :=
  (Erdos593.SimpleGraph.bridgeFree F.levi).ConnectedComponent

/-- Every bridge-free Levi component containing an edge incident with `x`
lies in the closed star of the component containing the point-node `x` in the
bridge quotient.  This is the hypergraph-facing running-intersection kernel. -/
theorem component_eq_or_leviBridgeQuotient_adj_of_inc
    {C : Component F} {x : V} {e : E}
    (heC : Sum.inr e ∈ C.supp) (hxe : F.Inc x e) :
    C = (Erdos593.SimpleGraph.bridgeFree F.levi).connectedComponentMk
          (Sum.inl x) ∨
      (Erdos593.SimpleGraph.bridgeQuotient F.levi).Adj C
        ((Erdos593.SimpleGraph.bridgeFree F.levi).connectedComponentMk
          (Sum.inl x)) := by
  exact Erdos593.SimpleGraph.eq_or_bridgeQuotient_adj_of_adj_mem_supp
    F.levi (F.levi_adj_point_edge.mpr hxe) heC

/-- The point-nodes lying in a bridge-free Levi component. -/
abbrev Point (C : Component F) :=
  {x : V // Sum.inl x ∈ C.supp}

/-- Hyperedge-nodes in `C` that genuinely contract to ordinary edges. -/
abbrev ContractibleEdge (C : Component F) :=
  {e : E //
    Sum.inr e ∈ C.supp ∧
      (Erdos593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 2}

/-- `C` contains a nonbridge incidence (equivalently, an edge of the
bridge-free Levi graph). -/
def HasIncidence (C : Component F) : Prop :=
  ∃ x : V, ∃ e : E,
    Sum.inl x ∈ C.supp ∧ Sum.inr e ∈ C.supp ∧
      (Erdos593.SimpleGraph.bridgeFree F.levi).Adj (Sum.inl x) (Sum.inr e)

/-- Contract every bridge-free degree-two hyperedge-node of `C` to an
ordinary edge between its two point-neighbours. -/
def contractedGraph (C : Component F) : _root_.SimpleGraph (Point F C) where
  Adj x y := x ≠ y ∧ ∃ e : ContractibleEdge F C,
    (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
        (Sum.inl x.1) (Sum.inr e.1) ∧
      (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
        (Sum.inl y.1) (Sum.inr e.1)
  symm := ⟨by
    rintro x y ⟨hxy, e, hxe, hye⟩
    exact ⟨hxy.symm, e, hye, hxe⟩⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

@[simp]
theorem contractedGraph_adj (C : Component F) (x y : Point F C) :
    (contractedGraph F C).Adj x y ↔
      x ≠ y ∧ ∃ e : ContractibleEdge F C,
        (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
            (Sum.inl x.1) (Sum.inr e.1) ∧
          (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
            (Sum.inl y.1) (Sum.inr e.1) :=
  Iff.rfl

/-- In a component containing a nonbridge incidence, every hyperedge-node
has bridge-free degree two. -/
theorem edge_degree_eq_two_of_hasIncidence
    (hbridge : F.BridgeAtEveryEdge)
    {C : Component F} (hC : HasIncidence F C)
    {e : E} (heC : Sum.inr e ∈ C.supp) :
    (Erdos593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) = 2 := by
  rcases F.levi_bridgeFree_edge_degree_eq_zero_or_two hbridge e with hzero | htwo
  · rcases hC with ⟨x, f, hxC, hfC, hxf⟩
    have hre : (Erdos593.SimpleGraph.bridgeFree F.levi).Reachable
        (Sum.inr e) (Sum.inl x) :=
      C.reachable_of_mem_supp heC hxC
    have hpos : 0 < (Erdos593.SimpleGraph.bridgeFree F.levi).degree (Sum.inr e) :=
      hre.degree_pos_left (by simp)
    omega
  · exact htwo

/-- Distinct degree-two hyperedge-nodes in one block cannot contract to the
same ordinary edge in a linear triple system. -/
theorem contractibleEdge_unique
    (hlinear : F.Linear)
    {C : Component F} {x y : Point F C}
    (hxy : x ≠ y)
    {e f : ContractibleEdge F C}
    (hxe : (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
      (Sum.inl x.1) (Sum.inr e.1))
    (hye : (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
      (Sum.inl y.1) (Sum.inr e.1))
    (hxf : (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
      (Sum.inl x.1) (Sum.inr f.1))
    (hyf : (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
      (Sum.inl y.1) (Sum.inr f.1)) :
    e = f := by
  have hle : Erdos593.SimpleGraph.bridgeFree F.levi ≤ F.levi := by
    dsimp only [Erdos593.SimpleGraph.bridgeFree]
    exact F.levi.deleteEdges_le _
  apply Subtype.ext
  by_contra hef
  apply hxy
  apply Subtype.ext
  apply hlinear hef
  · apply F.levi_adj_point_edge.mp
    exact hle hxe
  · apply F.levi_adj_point_edge.mp
    exact hle hxf
  · apply F.levi_adj_point_edge.mp
    exact hle hye
  · apply F.levi_adj_point_edge.mp
    exact hle hyf

/-- Adjacency in the contracted graph has a unique hyperedge witness under
linearity. -/
theorem contractedGraph_existsUnique_edge
    (hlinear : F.Linear)
    {C : Component F} {x y : Point F C}
    (hxy : (contractedGraph F C).Adj x y) :
    ∃! e : ContractibleEdge F C,
      (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
          (Sum.inl x.1) (Sum.inr e.1) ∧
        (Erdos593.SimpleGraph.bridgeFree F.levi).Adj
          (Sum.inl y.1) (Sum.inr e.1) := by
  rcases (contractedGraph_adj F C x y).mp hxy with ⟨hne, e, he⟩
  refine ⟨e, he, ?_⟩
  intro f hf
  exact (contractibleEdge_unique F hlinear hne (e := e) (f := f)
    he.1 he.2 hf.1 hf.2).symm

end BridgeBlock

end TripleSystem

end Erdos593
