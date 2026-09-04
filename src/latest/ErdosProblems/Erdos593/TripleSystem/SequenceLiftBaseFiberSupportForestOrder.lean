import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Leaf-elimination orders for finite forests

This is the graph-theoretic core needed when a support-overlap graph is
acyclic.  Every finite induced subgraph of a forest has an isolated vertex or
a leaf, so its vertices can be ordered such that each vertex has at most one
neighbour later in the order.
-/

namespace SimpleGraph

universe u

variable {V : Type u}

/-- `tailAtMostOneNeighbor G l` says that every vertex in the list has at
most one `G`-neighbour later in the list. -/
def tailAtMostOneNeighbor (G : SimpleGraph V) : List V → Prop
  | [] => True
  | q :: tail =>
      tailAtMostOneNeighbor G tail ∧
        ∀ u ∈ tail, ∀ w ∈ tail, G.Adj q u → G.Adj q w → u = w

/-- A nonempty finite acyclic graph has a vertex with at most one neighbour.

The result deliberately includes isolated vertices: this makes it apply to
arbitrary induced subgraphs during leaf elimination. -/
theorem IsAcyclic.exists_vertex_adj_unique
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] [Nonempty V]
    (hG : G.IsAcyclic) :
    ∃ q : V, ∀ ⦃u w : V⦄, G.Adj q u → G.Adj q w → u = w := by
  classical
  let x : V := Classical.choice (inferInstance : Nonempty V)
  by_cases hx : G.degree x = 0
  · refine ⟨x, ?_⟩
    intro u w hxu _
    have hpos : 0 < G.degree x := (G.degree_pos_iff_exists_adj x).mpr ⟨u, hxu⟩
    omega
  · have hpos : 0 < G.degree x := Nat.pos_of_ne_zero hx
    obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x).mp hpos
    let c : G.ConnectedComponent := G.connectedComponentMk x
    have hxc : x ∈ c := by
      exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem (G := G)
    have hyc : y ∈ c := c.mem_supp_of_adj_mem_supp hxc hxy
    have hne : (⟨x, hxc⟩ : c) ≠ ⟨y, hyc⟩ := by
      intro h
      exact hxy.ne (congrArg Subtype.val h)
    let : Nontrivial c := ⟨⟨x, hxc⟩, ⟨y, hyc⟩, hne⟩
    obtain ⟨q, hq⟩ := (hG.isTree_connectedComponent c).exists_vert_degree_one_of_nontrivial
    have huniq : ∃! z : c, c.toSimpleGraph.Adj q z :=
      (SimpleGraph.degree_eq_one_iff_existsUnique_adj).mp hq
    refine ⟨q, ?_⟩
    intro u w hqu hqw
    have huc : u ∈ c := c.mem_supp_of_adj_mem_supp q.property hqu
    have hwc : w ∈ c := c.mem_supp_of_adj_mem_supp q.property hqw
    have hqu' : c.toSimpleGraph.Adj q ⟨u, huc⟩ :=
      (c.toSimpleGraph_adj q.property huc).mpr hqu
    have hqw' : c.toSimpleGraph.Adj q ⟨w, hwc⟩ :=
      (c.toSimpleGraph_adj q.property hwc).mpr hqw
    exact congrArg Subtype.val (huniq.unique hqu' hqw')

/-- Every finite set of vertices in an acyclic graph has a noduplicated
leaf-elimination order.  In the resulting order each vertex has at most one
neighbour in its tail. -/
theorem IsAcyclic.exists_finset_tailAtMostOneNeighborOrder
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (s : Finset V) :
    ∃ l : List V, l.Nodup ∧ l.toFinset = s ∧ G.tailAtMostOneNeighbor l := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hs : s = ∅
    · subst s
      exact ⟨[], List.nodup_nil, by simp, trivial⟩
    · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
      let : Nonempty s := hsne.to_subtype
      obtain ⟨q, hq⟩ :=
        IsAcyclic.exists_vertex_adj_unique (hG.induce (↑s : Set V))
      obtain ⟨l, hlNodup, hlFinset, hlTail⟩ :=
        ih (s.erase q) (Finset.erase_ssubset q.property)
      refine ⟨q.val :: l, ?_, ?_, ?_⟩
      · rw [List.nodup_cons]
        refine ⟨?_, hlNodup⟩
        intro hqmem
        have hqerase : q.val ∈ s.erase q.val := by
          rw [← hlFinset]
          exact List.mem_toFinset.mpr hqmem
        exact (Finset.mem_erase.mp hqerase).1 rfl
      · rw [List.toFinset_cons, hlFinset, Finset.insert_erase q.property]
      · change
          tailAtMostOneNeighbor G l ∧
            ∀ u ∈ l, ∀ w ∈ l, G.Adj q.val u → G.Adj q.val w → u = w
        refine ⟨hlTail, ?_⟩
        intro u hu w hw hqu hqw
        have huerase : u ∈ s.erase q.val := by
          rw [← hlFinset]
          exact List.mem_toFinset.mpr hu
        have hwerase : w ∈ s.erase q.val := by
          rw [← hlFinset]
          exact List.mem_toFinset.mpr hw
        have hqu' : (G.induce (↑s : Set V)).Adj q
            ⟨u, Finset.mem_of_mem_erase huerase⟩ :=
          SimpleGraph.induce_adj.mpr hqu
        have hqw' : (G.induce (↑s : Set V)).Adj q
            ⟨w, Finset.mem_of_mem_erase hwerase⟩ :=
          SimpleGraph.induce_adj.mpr hqw
        exact congrArg Subtype.val (hq hqu' hqw')

/-- A finite acyclic graph has a noduplicated leaf-elimination order of all
of its vertices. -/
theorem IsAcyclic.exists_tailAtMostOneNeighborOrder
    {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsAcyclic) :
    ∃ l : List V, l.Nodup ∧ l.toFinset = Finset.univ ∧ G.tailAtMostOneNeighbor l :=
  hG.exists_finset_tailAtMostOneNeighborOrder Finset.univ

end SimpleGraph
