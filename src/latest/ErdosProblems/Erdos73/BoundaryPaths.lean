/- Boundary-proper paths and the local neighbor arguments used in rerouting. -/
import ErdosProblems.Erdos73.PackingCopy

namespace Erdos73Infrastructure.SimpleGraph
variable {V : Type*} [DecidableEq V] {G : _root_.SimpleGraph V}

namespace GraphPath

structure IsBoundaryProper (P : GraphPath G) (Z : Finset V) : Prop where
  source_mem : P.source ∈ Z
  target_mem : P.target ∈ Z
  internal_disjoint : P.InternallyDisjointFromSet Z
  length_ne_one : P.walk.length ≠ 1

theorem endpoint_neighbors_eq (P : GraphPath G) {v x y : V} (hv : P.IsEndpoint v)
    (hx : s(v, x) ∈ P.edgeSet) (hy : s(v, y) ∈ P.edgeSet) : x = y := by
  have hadjx : P.walk.toSubgraph.Adj v x :=
    _root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr (List.mem_toFinset.mp hx)
  have hadjy : P.walk.toSubgraph.Adj v y :=
    _root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr (List.mem_toFinset.mp hy)
  have hnn := _root_.SimpleGraph.Walk.not_nil_of_adj_toSubgraph hadjx
  rcases hv with rfl | rfl
  · exact (P.isPath.snd_of_toSubgraph_adj hadjx).symm.trans
      (P.isPath.snd_of_toSubgraph_adj hadjy)
  · have hN := P.isPath.neighborSet_toSubgraph_endpoint hnn
    have hxN : x ∈ P.walk.toSubgraph.neighborSet P.target := hadjx
    have hyN : y ∈ P.walk.toSubgraph.neighborSet P.target := hadjy
    rw [hN] at hxN hyN
    exact hxN.trans hyN.symm

theorem length_eq_one_of_endpoint_edge (P : GraphPath G)
    (he : s(P.source, P.target) ∈ P.edgeSet) : P.walk.length = 1 := by
  have hadj : P.walk.toSubgraph.Adj P.source P.target :=
    _root_.SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr (List.mem_toFinset.mp he)
  have hnn := _root_.SimpleGraph.Walk.not_nil_of_adj_toSubgraph hadj
  have hpos := _root_.SimpleGraph.Walk.not_nil_iff_lt_length.mp hnn
  have hs := P.isPath.snd_of_toSubgraph_adj hadj
  have heq : P.walk.getVert 1 = P.walk.getVert P.walk.length := by
    simpa only [_root_.SimpleGraph.Walk.getVert_length] using hs
  exact (P.isPath.getVert_injOn (by exact (show 1 ≤ P.walk.length by omega))
    (by exact (show P.walk.length ≤ P.walk.length from le_rfl)) heq).symm

theorem IsBoundaryProper.not_edge_between_boundary {P : GraphPath G} {Z : Finset V}
    (hP : P.IsBoundaryProper Z) {x y : V} (hxZ : x ∈ Z) (hyZ : y ∈ Z) :
    s(x, y) ∉ P.edgeSet := by
  intro hxy
  obtain ⟨hx, hy⟩ := P.endpoints_mem_vertexSet_of_edgeSet hxy
  have hne := (P.edgeSet_subset_edgeSet hxy).ne
  rcases hP.internal_disjoint hx hxZ with hxs | hxt <;>
    rcases hP.internal_disjoint hy hyZ with hys | hyt
  · exact hne (hxs.trans hys.symm)
  · exact hP.length_ne_one (P.length_eq_one_of_endpoint_edge (by simpa only [hxs, hyt] using hxy))
  · apply hP.length_ne_one
    apply P.length_eq_one_of_endpoint_edge
    simpa only [hxt, hys, Sym2.eq_swap] using hxy
  · exact hne (hxt.trans hyt.symm)

theorem IsBoundaryProper.mapLe {H : _root_.SimpleGraph V} {P : GraphPath G}
    {Z : Finset V} (hP : P.IsBoundaryProper Z) (hGH : G ≤ H) :
    (P.mapLe hGH).IsBoundaryProper Z := by
  refine ⟨hP.source_mem, hP.target_mem, ?_, ?_⟩
  · intro x hx hxZ
    rw [GraphPath.mapLe_vertexSet] at hx
    exact hP.internal_disjoint hx hxZ
  · simpa only [GraphPath.mapLe, _root_.SimpleGraph.Walk.length_mapLe] using hP.length_ne_one

theorem IsBoundaryProper.reverse {P : GraphPath G} {Z : Finset V}
    (hP : P.IsBoundaryProper Z) : P.reverse.IsBoundaryProper Z := by
  refine ⟨hP.target_mem, hP.source_mem, ?_, ?_⟩
  · intro x hx hxZ
    rw [GraphPath.reverse_vertexSet] at hx
    exact (hP.internal_disjoint hx hxZ).symm
  · simpa only [GraphPath.reverse, _root_.SimpleGraph.Walk.length_reverse] using hP.length_ne_one

theorem IsBoundaryProper.orient {P : GraphPath G} {Z S T : Finset V}
    (hP : P.IsBoundaryProper Z) (hc : P.Connects S T) : (P.orient hc).IsBoundaryProper Z := by
  unfold GraphPath.orient
  split
  · exact hP
  · exact hP.reverse

/-- At most one ambient neighbor forces every occurrence on a simple path
to be an endpoint. This also permits degree zero. -/
theorem isEndpoint_of_mem_vertexSet_of_neighbors_eq
    (P : GraphPath G) {v : V}
    (hneighbors : ∀ x y, G.Adj v x → G.Adj v y → x = y) (hv : v ∈ P.vertexSet) :
    P.IsEndpoint v := by
  classical
  by_cases hsource : v = P.source
  · exact Or.inl hsource
  by_cases htarget : v = P.target
  · exact Or.inr htarget
  exfalso
  have hvSupport : v ∈ P.walk.support := by
    simpa [vertexSet] using hv
  rcases _root_.SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hvSupport with
    ⟨n, hn, hnle⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hsource
    simpa [hn0] using hn.symm
  have hn_lt_length : n < P.walk.length := by
    by_contra hnot
    have hnlen : n = P.walk.length := by omega
    apply htarget
    simpa [hnlen] using hn.symm
  have hprev_adj :
      G.Adj v (P.walk.getVert (n - 1)) := by
    have hsub :
        P.walk.toSubgraph.Adj (P.walk.getVert (n - 1))
          (P.walk.getVert ((n - 1) + 1)) :=
      P.walk.toSubgraph_adj_getVert (by omega)
    have hsub' :
        P.walk.toSubgraph.Adj (P.walk.getVert (n - 1)) v := by
      simpa [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn_ne_zero), hn] using hsub
    exact (P.walk.toSubgraph.adj_sub hsub').symm
  have hnext_adj :
      G.Adj v (P.walk.getVert (n + 1)) := by
    have hsub :
        P.walk.toSubgraph.Adj (P.walk.getVert n)
          (P.walk.getVert (n + 1)) :=
      P.walk.toSubgraph_adj_getVert hn_lt_length
    have hsub' :
        P.walk.toSubgraph.Adj v (P.walk.getVert (n + 1)) := by
      simpa [hn] using hsub
    exact P.walk.toSubgraph.adj_sub hsub'
  have hprev_ne_next :
      P.walk.getVert (n - 1) ≠ P.walk.getVert (n + 1) := by
    intro hsame
    have hidx := P.isPath.getVert_injOn
      (by exact (show n - 1 ≤ P.walk.length by omega))
      (by exact (show n + 1 ≤ P.walk.length by omega))
      hsame
    omega
  exact hprev_ne_next (hneighbors _ _ hprev_adj hnext_adj)

end GraphPath

namespace PathPacking
variable {A B : Finset V}

def IsBoundaryProper (P : PathPacking G A B) (Z : Finset V) : Prop :=
  ∀ i, (P.path i).IsBoundaryProper Z

theorem IsBoundaryProper.restrictIndexSet {P : PathPacking G A B} {Z : Finset V}
    (hP : P.IsBoundaryProper Z) (S : Finset P.Index) :
    (P.restrictIndexSet S).IsBoundaryProper Z := fun i => hP i.val

theorem not_adj_spanningGraph_of_not_mem_vertexSet (P : PathPacking G A B)
    {x y : V} (hx : x ∉ P.vertexSet) : ¬ P.spanningGraph.Adj x y := by
  intro hxy
  obtain ⟨⟨i, hi⟩, _⟩ := P.spanningGraph_adj_iff_exists_path_edge.mp hxy
  exact hx (P.mem_vertexSet.mpr ⟨i, ((P.path i).endpoints_mem_vertexSet_of_edgeSet hi).1⟩)

theorem IsBoundaryProper.no_boundary_edge {P : PathPacking G A B} {Z : Finset V}
    (hP : P.IsBoundaryProper Z) {x y : V} (hx : x ∈ Z) (hy : y ∈ Z) :
    ¬ P.spanningGraph.Adj x y := by
  intro hxy
  obtain ⟨⟨i, hi⟩, _⟩ := P.spanningGraph_adj_iff_exists_path_edge.mp hxy
  exact (hP i).not_edge_between_boundary hx hy hi

theorem IsBoundaryProper.boundary_neighbors_eq {P : PathPacking G A B} {Z : Finset V}
    (hP : P.IsBoundaryProper Z) {v x y : V} (hv : v ∈ Z)
    (hx : P.spanningGraph.Adj v x) (hy : P.spanningGraph.Adj v y) : x = y := by
  obtain ⟨⟨i, hi⟩, _⟩ := P.spanningGraph_adj_iff_exists_path_edge.mp hx
  obtain ⟨⟨j, hj⟩, _⟩ := P.spanningGraph_adj_iff_exists_path_edge.mp hy
  have hvi := ((P.path i).endpoints_mem_vertexSet_of_edgeSet hi).1
  have hvj := ((P.path j).endpoints_mem_vertexSet_of_edgeSet hj).1
  have hij : i = j := by
    by_contra h
    exact Finset.disjoint_left.mp (P.node_disjoint h) hvi hvj
  subst j
  exact (P.path i).endpoint_neighbors_eq ((hP i).internal_disjoint hvi hv) hi hj

theorem IsBoundaryProper.not_mem_vertexSet_of_not_mem_terminals
    {P : PathPacking G A B} {Z : Finset V} (hP : P.IsBoundaryProper Z)
    {x : V} (hxZ : x ∈ Z) (hxAB : x ∉ A ∪ B) : x ∉ P.vertexSet := by
  intro hx
  obtain ⟨i, hi⟩ := P.mem_vertexSet.mp hx
  have hend := (hP i).internal_disjoint hi hxZ
  rcases P.connects i with hc | hc <;> rcases hend with rfl | rfl
  · exact hxAB (Finset.mem_union_left _ hc.1)
  · exact hxAB (Finset.mem_union_right _ hc.2)
  · exact hxAB (Finset.mem_union_right _ hc.1)
  · exact hxAB (Finset.mem_union_left _ hc.2)

end PathPacking
end Erdos73Infrastructure.SimpleGraph
