import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Deleting all bridge edges

Finite graph infrastructure for the bridge-block decomposition of a Levi graph.
-/

namespace Erdos593

namespace SimpleGraph

open scoped Sym2

universe u

variable {V : Type u}

/-- The finite set of actual bridge edges of a finite simple graph. -/
noncomputable def bridgeFinset (G : _root_.SimpleGraph V) [Fintype G.edgeSet] :
    Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter G.IsBridge

@[simp]
lemma mem_bridgeFinset {G : _root_.SimpleGraph V} [Fintype G.edgeSet] {e : Sym2 V} :
    e ∈ bridgeFinset G ↔ e ∈ G.edgeSet ∧ G.IsBridge e := by
  classical
  simp [bridgeFinset]

/-- The graph obtained by deleting every actual bridge edge. -/
noncomputable def bridgeFree (G : _root_.SimpleGraph V) [Fintype G.edgeSet]
    [DecidableEq V] : _root_.SimpleGraph V :=
  G.deleteEdges (bridgeFinset G : Set (Sym2 V))

noncomputable instance instDecidableRelBridgeFree (G : _root_.SimpleGraph V)
    [Fintype G.edgeSet] [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (bridgeFree G).Adj := by
  unfold bridgeFree
  infer_instance

/-- After all actual bridges are deleted, no vertex has degree exactly one. -/
lemma bridgeFree_degree_ne_one [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (bridgeFree G).degree v ≠ 1 := by
  classical
  let B : Set (Sym2 V) := bridgeFinset G
  let H : _root_.SimpleGraph V := G.deleteEdges B
  change H.degree v ≠ 1
  intro hdeg
  obtain ⟨w, hvw, huniq⟩ :=
    (_root_.SimpleGraph.degree_eq_one_iff_existsUnique_adj (G := H) (v := v)).mp hdeg
  have hvwG : G.Adj v w ∧ s(v, w) ∉ B := by
    simpa [H] using! hvw
  have hnbridge : ¬G.IsBridge s(v, w) := by
    intro hb
    have hmem : s(v, w) ∈ bridgeFinset G :=
      mem_bridgeFinset.mpr ⟨hvwG.1, hb⟩
    exact hvwG.2 (by simpa [B] using! hmem)
  have hreach : (G.deleteEdges {s(v, w)}).Reachable v w := by
    rw [_root_.SimpleGraph.isBridge_iff] at hnbridge
    exact not_not.mp hnbridge
  obtain ⟨u, c, hc, hmem⟩ :=
    (_root_.SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle
      (G := G) (v := v) (w := w)).mp ⟨hvwG.1, hreach⟩
  have havoid : ∀ e, e ∈ c.edges → e ∉ B := by
    intro e he hbe
    have hbe' : e ∈ bridgeFinset G := by simpa [B] using! hbe
    exact (mem_bridgeFinset.mp hbe').2.notMem_edges_of_isCycle hc he
  let cH : H.Walk u u := c.toDeleteEdges B havoid
  have hcH : cH.IsCycle := by
    dsimp [cH]
    exact _root_.SimpleGraph.Walk.IsCycle.toDeleteEdges (G := G) B hc havoid
  have hedges : cH.edges = c.edges := by
    dsimp [cH, _root_.SimpleGraph.Walk.toDeleteEdges]
    apply _root_.SimpleGraph.Walk.edges_transfer
  have hmemH : s(v, w) ∈ cH.edges := by
    rw [hedges]
    exact hmem
  have hv : v ∈ cH.support := cH.fst_mem_support_of_mem_edges hmemH
  let r := cH.rotate v hv
  have hr : r.IsCycle := hcH.rotate hv
  have hsnd : H.Adj v r.snd := r.adj_snd hr.not_nil
  have hpen : H.Adj v r.penultimate := (r.adj_penultimate hr.not_nil).symm
  exact hr.snd_ne_penultimate ((huniq _ hsnd).trans (huniq _ hpen).symm)

/-- Deleting all actual bridges strictly lowers the degree at an endpoint of a bridge. -/
lemma bridgeFree_degree_lt_of_adj_isBridge [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] {v w : V}
    (hvw : G.Adj v w) (hb : G.IsBridge s(v, w)) :
    (bridgeFree G).degree v < G.degree v := by
  classical
  let H : _root_.SimpleGraph V := bridgeFree G
  change H.degree v < G.degree v
  have hle : H ≤ G := by
    dsimp [H, bridgeFree]
    exact G.deleteEdges_le _
  have hsub : H.neighborFinset v ⊆ G.neighborFinset v := by
    intro x hx
    rw [_root_.SimpleGraph.mem_neighborFinset] at hx ⊢
    exact hle hx
  have hwG : w ∈ G.neighborFinset v := by
    simpa using! hvw
  have hwH : w ∉ H.neighborFinset v := by
    simp [H, bridgeFree, hvw, hb]
  have hssub : H.neighborFinset v ⊂ G.neighborFinset v := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨hsub, ?_⟩
    intro heq
    apply hwH
    rw [heq]
    exact hwG
  simpa only [_root_.SimpleGraph.card_neighborFinset_eq_degree] using!
    Finset.card_lt_card hssub

/-- A degree-three vertex incident with an actual bridge has bridge-free degree zero or two. -/
theorem bridgeFree_degree_eq_zero_or_two [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (hdeg : G.degree v = 3)
    (hbridge : ∃ w, G.Adj v w ∧ G.IsBridge s(v, w)) :
    (bridgeFree G).degree v = 0 ∨ (bridgeFree G).degree v = 2 := by
  classical
  obtain ⟨w, hvw, hb⟩ := hbridge
  have hlt := bridgeFree_degree_lt_of_adj_isBridge G hvw hb
  have hne_one := bridgeFree_degree_ne_one G v
  omega

/-- A bridge is the unique graph edge joining its two bridge-free components.
This is the simplicity input for the later quotient forest. -/
theorem edge_eq_of_bridgeFree_reachable_endpoints_of_isBridge
    [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) [DecidableRel G.Adj]
    {u v x y : V}
    (hAdj : G.Adj u v) (hBridge : G.IsBridge s(u, v))
    (hxy : G.Adj x y)
    (hux : (bridgeFree G).Reachable u x)
    (hvy : (bridgeFree G).Reachable v y) :
    s(x, y) = s(u, v) := by
  by_contra hne
  have hBridgeOriginal := hBridge
  rw [_root_.SimpleGraph.isBridge_iff] at hBridge
  apply hBridge
  have hmono : (bridgeFree G).Adj ≤
      (G.deleteEdges {s(u, v)}).Adj := by
    intro a b hab
    rw [bridgeFree, _root_.SimpleGraph.deleteEdges_adj] at hab
    rw [_root_.SimpleGraph.deleteEdges_adj]
    apply And.intro hab.1
    intro hmem
    have heq := Set.mem_singleton_iff.mp hmem
    apply hab.2
    rw [heq]
    exact mem_bridgeFinset.mpr (And.intro hAdj hBridgeOriginal)
  have hux' := hux.mono hmono
  have hvy' := hvy.mono hmono
  have hxy' : (G.deleteEdges {s(u, v)}).Adj x y := by
    rw [_root_.SimpleGraph.deleteEdges_adj]
    exact And.intro hxy (by simpa using! hne)
  exact hux'.trans (hxy'.reachable.trans hvy'.symm)

end SimpleGraph

end Erdos593
