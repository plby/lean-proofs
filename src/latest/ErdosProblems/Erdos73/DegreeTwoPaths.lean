import ErdosProblems.Erdos73.BoundaryPaths

/-! A component of maximum degree two containing a degree-one vertex is a path. -/

namespace Erdos73Infrastructure.SimpleGraph

open _root_.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : _root_.SimpleGraph V}

def AtMostTwoNeighbors (G : _root_.SimpleGraph V) : Prop :=
  ∀ v a b c, G.Adj v a → G.Adj v b → G.Adj v c → a = b ∨ a = c ∨ b = c

namespace GraphPath

omit [DecidableEq V] in
theorem exists_longest_from (G : _root_.SimpleGraph V) (x : V) :
    ∃ P : GraphPath G, P.source = x ∧
      ∀ Q : GraphPath G, Q.source = x → Q.walk.length ≤ P.walk.length := by
  let lengths : Set ℕ := {n | ∃ P : GraphPath G, P.source = x ∧ P.walk.length = n}
  have hfin : lengths.Finite := (Set.finite_lt_nat (Fintype.card V)).subset (by
    rintro n ⟨P, _, rfl⟩
    exact P.isPath.length_lt)
  have hne : lengths.Nonempty := ⟨0, refl G x, rfl, rfl⟩
  obtain ⟨n, ⟨⟨P, hP, hlen⟩, hmax⟩⟩ := hfin.exists_maximal hne
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  have hh := hmax (show Q.walk.length ∈ lengths from ⟨Q, hQ, rfl⟩)
  omega

omit [Fintype V] in
theorem internal_neighbors (P : GraphPath G) {v : V} (hv : v ∈ P.vertexSet)
    (hs : v ≠ P.source) (ht : v ≠ P.target) :
    ∃ a b, a ≠ b ∧ s(v, a) ∈ P.edgeSet ∧ s(v, b) ∈ P.edgeSet := by
  obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp
    (show v ∈ P.walk.support from List.mem_toFinset.mp hv)
  have hi0 : 0 < i := by
    by_contra h
    have : i = 0 := by omega
    exact hs (by simpa [this] using hi.symm)
  have hil : i < P.walk.length := by
    by_contra h
    have : i = P.walk.length := by omega
    exact ht (by simpa [this] using hi.symm)
  refine ⟨P.walk.getVert (i - 1), P.walk.getVert (i + 1), ?_, ?_, ?_⟩
  · intro he
    have hh := P.isPath.getVert_injOn (show i - 1 ≤ P.walk.length by omega)
      (show i + 1 ≤ P.walk.length by omega) he
    omega
  · apply List.mem_toFinset.mpr
    apply Walk.adj_toSubgraph_iff_mem_edges.mp
    have hh := (P.walk.toSubgraph_adj_getVert (show i - 1 < P.walk.length by omega)).symm
    simpa only [Nat.sub_add_cancel hi0, hi] using hh
  · apply List.mem_toFinset.mpr
    apply Walk.adj_toSubgraph_iff_mem_edges.mp
    simpa only [hi] using P.walk.toSubgraph_adj_getVert hil

omit [Fintype V] in
theorem neighbor_mem_of_internal (P : GraphPath G) (hG : AtMostTwoNeighbors G)
    {v w : V} (hv : v ∈ P.vertexSet) (hs : v ≠ P.source) (ht : v ≠ P.target)
    (hvw : G.Adj v w) : w ∈ P.vertexSet := by
  obtain ⟨a, b, hab, ha, hb⟩ := P.internal_neighbors hv hs ht
  have hcase := hG v a b w (P.edgeSet_subset_edgeSet ha)
    (P.edgeSet_subset_edgeSet hb) hvw
  rcases hcase with h | h | h
  · exact (hab h).elim
  · exact h ▸ (P.endpoints_mem_vertexSet_of_edgeSet ha).2
  · exact h ▸ (P.endpoints_mem_vertexSet_of_edgeSet hb).2

theorem exists_closed_path_from_degree_one (hG : AtMostTwoNeighbors G) (x : V)
    (hx : ∃ y, G.Adj x y) (hdeg : ∀ a b, G.Adj x a → G.Adj x b → a = b) :
    ∃ P : GraphPath G, P.source = x ∧ P.source ≠ P.target ∧
      ∀ v ∈ P.vertexSet, ∀ w, G.Adj v w → w ∈ P.vertexSet := by
  obtain ⟨P, hsource, hmax⟩ := exists_longest_from G x
  have hpos : 0 < P.walk.length := by
    obtain ⟨y, hxy⟩ := hx
    let Q : GraphPath G := ⟨x, y, Walk.cons hxy Walk.nil, by simp [hxy.ne]⟩
    have hh := hmax Q rfl
    change 1 ≤ P.walk.length at hh
    omega
  have hne : P.source ≠ P.target := by
    intro he
    have hh := P.isPath.getVert_injOn (show 0 ≤ P.walk.length by omega)
      (show P.walk.length ≤ P.walk.length from le_rfl)
      (show P.walk.getVert 0 = P.walk.getVert P.walk.length by simpa using he)
    omega
  have htarget : ∀ w, G.Adj P.target w → w ∈ P.vertexSet := by
    intro w hw
    by_contra hn
    let Q : GraphPath G := ⟨w, P.source, Walk.cons hw.symm P.walk.reverse,
      by
        apply Walk.IsPath.cons P.isPath.reverse
        simpa only [Walk.support_reverse, List.mem_reverse, vertexSet,
          List.mem_toFinset] using hn⟩
    have hh := hmax Q.reverse hsource
    have hl : Q.reverse.walk.length = P.walk.length + 1 := by
      simp [Q, GraphPath.reverse]
    omega
  refine ⟨P, hsource, hne, ?_⟩
  intro v hv w hvw
  by_cases hs : v = P.source
  · have hfirst := P.walk.toSubgraph_adj_getVert hpos
    have hadj : G.Adj P.source (P.walk.getVert 1) := by
      simpa only [Walk.getVert_zero, zero_add] using P.walk.toSubgraph.adj_sub hfirst
    have he := hdeg w (P.walk.getVert 1) (by simpa only [hs, hsource] using hvw)
      (by simpa only [hsource] using hadj)
    rw [he]
    exact List.mem_toFinset.mpr (P.walk.getVert_mem_support 1)
  · by_cases ht : v = P.target
    · exact htarget w (by simpa only [ht] using hvw)
    · exact P.neighbor_mem_of_internal hG hv hs ht hvw

omit [Fintype V] in
theorem vertexSet_eq_component_of_closed (P : GraphPath G)
    (hclosed : ∀ v ∈ P.vertexSet, ∀ w, G.Adj v w → w ∈ P.vertexSet) :
    (P.vertexSet : Set V) = (G.connectedComponentMk P.source).supp := by
  ext v
  constructor
  · intro hv
    have hr : G.Reachable P.source v :=
      ⟨P.walk.takeUntil v (List.mem_toFinset.mp hv)⟩
    exact (ConnectedComponent.mem_supp_iff _ _).mpr (ConnectedComponent.sound hr.symm)
  · intro hv
    have hr : G.Reachable P.source v := ConnectedComponent.reachable_of_mem_supp _
      (ConnectedComponent.mem_supp_iff _ _ |>.mpr rfl) hv
    obtain ⟨p⟩ := hr
    have hprop : ∀ {u w : V} (q : G.Walk u w), u ∈ P.vertexSet → w ∈ P.vertexSet := by
      intro u w q
      induction q with
      | nil => exact id
      | cons hadj q ih =>
        intro hu
        exact ih (hclosed _ hu _ hadj)
    exact hprop p P.source_mem_vertexSet

end GraphPath
end Erdos73Infrastructure.SimpleGraph
