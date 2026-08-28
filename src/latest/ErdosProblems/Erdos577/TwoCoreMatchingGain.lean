import ErdosProblems.Erdos577.TwoCoreReplacementGeometry
import ErdosProblems.Erdos577.SelectedMatchingScore

/-! The global matching bound forces the distinguished core vertex to have degree three. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem replacement_edges_le {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (h3 : G.Adj p.leaf (q 3))
    (z : V) (hz : z ∈ b)
    (hBrep : QuadOn G (insert (p.vertices 3) (b.erase z)))
    (hQrep : QuadOn G (insert z (q.support.erase (q 3)))) :
    edgeCount G (insert (p.vertices 3) (b.erase z)) +
      edgeCount G (insert z (q.support.erase (q 3))) ≤
        edgeCount G b + edgeCount G q.support + 1 := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hpB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hQB : Disjoint q.support b := by
    rw [hq]
    exact c.property.blocks_disjoint hs hb hbs.symm
  let parts := (BlockPartition.single hBrep).union (BlockPartition.single hQrep)
    (replacement_blocks_disjoint p q hd b hpB hQB z hz)
  have hsel : ({b, s} : Finset (Finset V)) ⊆ c.blocks :=
    insert_subset hb (singleton_subset_iff.mpr hs)
  have hcore : c.remainder ∪ ({b, s} : Finset (Finset V)).biUnion id =
      p.support ∪ (b ∪ q.support) := by
    simp only [biUnion_insert, singleton_biUnion, id_eq, hp, hq]
  have hsub : insert (p.vertices 3) (b.erase z) ∪ insert z (q.support.erase (q 3)) ⊆
      c.remainder ∪ ({b, s} : Finset (Finset V)).biUnion id := by
    rw [hcore]
    exact replacement_subset p q b hQB z hz
  have hrem : (TwoEdges.ofPath (exposedPath p q hd h3)).support =
      (c.remainder ∪ ({b, s} : Finset (Finset V)).biUnion id) \
        (insert (p.vertices 3) (b.erase z) ∪ insert z (q.support.erase (q 3))) := by
    rw [TwoEdges.ofPath_support, hcore]
    exact (replacement_remainder p q hd b hpB hQB z hz h3).symm
  have hbound := hc.selected_matching_edges_le hcard hdeg hn {b, s} hsel parts hsub
    (TwoEdges.ofPath (exposedPath p q hd h3)) hrem
  have hold : (c.complementPartition.select {b, s} hsel).weightSum (edgeCount G) =
      edgeCount G b + edgeCount G s := by
    change ∑ t ∈ ({b, s} : Finset (Finset V)), edgeCount G t = _
    exact sum_pair hbs
  rw [BlockPartition.weightSum_union, BlockPartition.weightSum_single,
    BlockPartition.weightSum_single, hold, ← hq] at hbound
  exact hbound

theorem first_vertex_replacement {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (h3 : G.Adj p.leaf (q 3))
    (hdiag : PawBlock.OnlyFirst q) (z : V) (hz : z ∈ b)
    (hzQ : ∀ i : Fin 4, i ≠ 3 → G.Adj z (q i))
    (hfull : degreeIn G (p.vertices 3) b = 4) :
    degreeIn G z b = 3 ∧ QuadOn G (insert (p.vertices 3) (b.erase z)) ∧
      edgeCount G (insert (p.vertices 3) (b.erase z)) = edgeCount G b := by
  obtain ⟨_, hQrep, hQscore⟩ := third_replacement q z hdiag hzQ
  obtain ⟨hBrep, hBscore⟩ := full_replacement_score (c.property.blocks_quad b hb)
    (p.vertices 3) hfull z hz
  have hbound := replacement_edges_le hc hcard hdeg hn p hp hb hs hbs q hq h3 z hz hBrep hQrep
  have hcases := quad_vertex_degree (c.property.blocks_quad b hb) z hz
  have hzdegree : degreeIn G z b = 3 := by omega
  exact ⟨hzdegree, hBrep, by omega⟩

end Erdos577.TwoCore
