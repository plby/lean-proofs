import ErdosProblems.Erdos593.Graph.BridgeFree

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Bridge-component quotient forest

The quotient whose vertices are the connected components after deleting all
actual bridges, and whose edges are the surviving cross-component edges of the
original graph.
-/

namespace Erdos593
namespace SimpleGraph

open scoped Sym2

universe u

variable {V : Type u}

/-- Contract every connected component of `bridgeFree G` to one vertex. -/
noncomputable def bridgeQuotient (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] [DecidableEq V] :
    _root_.SimpleGraph (bridgeFree G).ConnectedComponent :=
  G.map (bridgeFree G).connectedComponentMk

theorem bridgeQuotient_adj_iff [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    (C D : (bridgeFree G).ConnectedComponent) :
    (bridgeQuotient G).Adj C D ↔
      C ≠ D ∧ ∃ u v : V, G.Adj u v ∧ u ∈ C.supp ∧ v ∈ D.supp := by
  change (G.map (bridgeFree G).connectedComponentMk).Adj C D ↔ _
  rw [_root_.SimpleGraph.map_adj']
  constructor
  · rintro ⟨hCD, u, v, huv, hu, hv⟩
    exact ⟨hCD, u, v, huv,
      by simpa [_root_.SimpleGraph.ConnectedComponent.mem_supp_iff] using! hu,
      by simpa [_root_.SimpleGraph.ConnectedComponent.mem_supp_iff] using! hv⟩
  · rintro ⟨hCD, u, v, huv, hu, hv⟩
    exact ⟨hCD, u, v, huv,
      by simpa [_root_.SimpleGraph.ConnectedComponent.mem_supp_iff] using! hu,
      by simpa [_root_.SimpleGraph.ConnectedComponent.mem_supp_iff] using! hv⟩

/-- Every original edge crossing two bridge-free components is an actual bridge. -/
theorem isBridge_of_mem_bridgeFree_components [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {C D : (bridgeFree G).ConnectedComponent} (hCD : C ≠ D)
    {u v : V} (huv : G.Adj u v) (hu : u ∈ C.supp) (hv : v ∈ D.supp) :
    G.IsBridge s(u, v) := by
  by_contra hnot
  have hfree : (bridgeFree G).Adj u v := by
    rw [bridgeFree, _root_.SimpleGraph.deleteEdges_adj]
    refine ⟨huv, ?_⟩
    intro hmem
    exact hnot (mem_bridgeFinset.mp hmem).2
  apply hCD
  have hu' : (bridgeFree G).connectedComponentMk u = C :=
    (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff C u).mp hu
  have hv' : (bridgeFree G).connectedComponentMk v = D :=
    (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff D v).mp hv
  exact hu'.symm.trans
    ((_root_.SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hfree).trans hv')

/-- Two original edges crossing the same ordered pair of bridge-free components
are the same unordered edge. -/
theorem bridgeQuotient_originalEdge_unique [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {C D : (bridgeFree G).ConnectedComponent} (hCD : C ≠ D)
    {u v x y : V}
    (huv : G.Adj u v) (hu : u ∈ C.supp) (hv : v ∈ D.supp)
    (hxy : G.Adj x y) (hx : x ∈ C.supp) (hy : y ∈ D.supp) :
    s(x, y) = s(u, v) := by
  apply edge_eq_of_bridgeFree_reachable_endpoints_of_isBridge G huv
    (isBridge_of_mem_bridgeFree_components G hCD huv hu hv) hxy
  · exact C.reachable_of_mem_supp hu hx
  · exact D.reachable_of_mem_supp hv hy

/-- A walk in the quotient avoiding one quotient edge lifts to reachability in
the original graph avoiding the unique original bridge over that edge. -/
theorem reachable_delete_of_bridgeQuotient_walk [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {C D : (bridgeFree G).ConnectedComponent} (hCD : C ≠ D)
    {u v : V} (huv : G.Adj u v) (hu : u ∈ C.supp) (hv : v ∈ D.supp)
    {A B : (bridgeFree G).ConnectedComponent}
    (p : ((bridgeQuotient G).deleteEdges {s(C, D)}).Walk A B)
    {a b : V} (ha : a ∈ A.supp) (hb : b ∈ B.supp) :
    (G.deleteEdges {s(u, v)}).Reachable a b := by
  have hBridge : G.IsBridge s(u, v) :=
    isBridge_of_mem_bridgeFree_components G hCD huv hu hv
  have hfreeMono : (bridgeFree G).Adj ≤
      (G.deleteEdges {s(u, v)}).Adj := by
    intro x y hxy
    rw [bridgeFree, _root_.SimpleGraph.deleteEdges_adj] at hxy
    rw [_root_.SimpleGraph.deleteEdges_adj]
    refine ⟨hxy.1, ?_⟩
    intro hmem
    have heq : s(x, y) = s(u, v) := Set.mem_singleton_iff.mp hmem
    apply hxy.2
    rw [heq]
    exact mem_bridgeFinset.mpr ⟨huv, hBridge⟩
  induction p generalizing a b with
  | @nil A =>
      exact (A.reachable_of_mem_supp ha hb).mono hfreeMono
  | @cons A X B hAX p ih =>
      rw [_root_.SimpleGraph.deleteEdges_adj] at hAX
      rcases hAX with ⟨hAX, hAXnot⟩
      rcases (bridgeQuotient_adj_iff G A X).mp hAX with
        ⟨hAneX, x, y, hxy, hxA, hyX⟩
      have hax : (G.deleteEdges {s(u, v)}).Reachable a x :=
        (A.reachable_of_mem_supp ha hxA).mono hfreeMono
      have hxyDel : (G.deleteEdges {s(u, v)}).Adj x y := by
        rw [_root_.SimpleGraph.deleteEdges_adj]
        refine ⟨hxy, ?_⟩
        intro hmem
        have hEdgeEq : s(x, y) = s(u, v) :=
          Set.mem_singleton_iff.mp hmem
        have hxA' : (bridgeFree G).connectedComponentMk x = A :=
          (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff A x).mp hxA
        have hyX' : (bridgeFree G).connectedComponentMk y = X :=
          (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff X y).mp hyX
        have huC' : (bridgeFree G).connectedComponentMk u = C :=
          (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff C u).mp hu
        have hvD' : (bridgeFree G).connectedComponentMk v = D :=
          (_root_.SimpleGraph.ConnectedComponent.mem_supp_iff D v).mp hv
        have hQuotientEdgeEq : s(A, X) = s(C, D) := by
          have hmap := congrArg
            (fun e : Sym2 V => e.map
              (bridgeFree G).connectedComponentMk) hEdgeEq
          simpa [hxA', hyX', huC', hvD'] using! hmap
        exact hAXnot (by simpa using! hQuotientEdgeEq)
      exact hax.trans (hxyDel.reachable.trans (ih hyX hb))

/-- Contracting the connected components left after deleting all actual
bridges always produces a forest. -/
theorem bridgeQuotient_isAcyclic [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] :
    (bridgeQuotient G).IsAcyclic := by
  rw [_root_.SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro C D hCDadj
  rcases (bridgeQuotient_adj_iff G C D).mp hCDadj with
    ⟨hCD, u, v, huv, hu, hv⟩
  have hBridge : G.IsBridge s(u, v) :=
    isBridge_of_mem_bridgeFree_components G hCD huv hu hv
  rw [_root_.SimpleGraph.isBridge_iff]
  rintro ⟨p⟩
  rw [_root_.SimpleGraph.isBridge_iff] at hBridge
  exact hBridge
    (reachable_delete_of_bridgeQuotient_walk G hCD huv hu hv p hu hv)

/-- Every bridge-free component containing a neighbour of `x` lies in the
closed star of the component containing `x` in the bridge quotient. -/
theorem eq_or_bridgeQuotient_adj_of_adj_mem_supp
    [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {C : (bridgeFree G).ConnectedComponent} {x y : V}
    (hxy : G.Adj x y) (hy : y ∈ C.supp) :
    C = (bridgeFree G).connectedComponentMk x ∨
      (bridgeQuotient G).Adj C
        ((bridgeFree G).connectedComponentMk x) := by
  by_cases hC : C = (bridgeFree G).connectedComponentMk x
  · exact Or.inl hC
  · exact Or.inr ((bridgeQuotient_adj_iff G C
      ((bridgeFree G).connectedComponentMk x)).mpr
        ⟨hC, y, x, hxy.symm, hy,
          _root_.SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩)

end SimpleGraph
end Erdos593
