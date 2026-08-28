import ErdosProblems.Erdos577.FullLeafHeavyScoreGeometry

/-! Separate triangle and matching score bounds for the same exact core insertion. -/

namespace Erdos577.FullLeafHeavy

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem insertion_triangle_bound {c : TriangleChain G} (hc : c.Feasible)
    {a j : Finset V} (ha : a ∈ c.blocks) (hj : j ∈ c.blocks) (haj : a ≠ j)
    {v : V} (hv : v ∈ j) (f : BlockPartition G (insert v (c.triangle ∪ a)))
    (htri : TriangleIn G (insert c.terminal (j.erase v))) :
    f.weightSum (edgeCount G) ≤ edgeCount G a + edgeCount G j := by
  have hsel : ({a, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset ha (singleton_subset_iff.mpr hj)
  have hsub := insertion_subset c (a := a) hv
  have hrem := insertion_complement c ha hj haj hv
  have hb := hc.selected_edges_le {a, j} hsel f
    (by simpa only [biUnion_insert, singleton_biUnion, id_eq] using hsub)
    (by simpa only [biUnion_insert, singleton_biUnion, id_eq, hrem] using
      insertion_remainder_card c hj hv)
    (by simpa only [biUnion_insert, singleton_biUnion, id_eq, hrem] using htri)
  have he : (c.complementPartition.select {a, j} hsel).weightSum (edgeCount G) =
      edgeCount G a + edgeCount G j := by
    change (∑ s ∈ ({a, j} : Finset (Finset V)), edgeCount G s) = _
    exact sum_pair haj
  rwa [he] at hb

theorem insertion_matching_bound {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {a j : Finset V} (ha : a ∈ c.blocks) (hj : j ∈ c.blocks) (haj : a ≠ j)
    {v : V} (hv : v ∈ j) (f : BlockPartition G (insert v (c.triangle ∪ a)))
    (m : TwoEdges G) (hm : m.support = insert c.terminal (j.erase v)) :
    f.weightSum (edgeCount G) ≤ edgeCount G a + edgeCount G j + 1 := by
  have hsel : ({a, j} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset ha (singleton_subset_iff.mpr hj)
  have hsub := insertion_subset c (a := a) hv
  have hrem := insertion_complement c ha hj haj hv
  have hb := hc.selected_matching_edges_le hcard hdeg hn {a, j} hsel f
    (by simpa only [biUnion_insert, singleton_biUnion, id_eq] using hsub) m
    (by simpa only [biUnion_insert, singleton_biUnion, id_eq, hrem] using hm)
  have he : (c.complementPartition.select {a, j} hsel).weightSum (edgeCount G) =
      edgeCount G a + edgeCount G j := by
    change (∑ s ∈ ({a, j} : Finset (Finset V)), edgeCount G s) = _
    exact sum_pair haj
  rwa [he] at hb

end Erdos577.FullLeafHeavy
