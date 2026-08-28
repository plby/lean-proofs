import ErdosProblems.Erdos577.TwoExposedRoutes

/-! TeX9.68: corrected Wang4.14, including the direct and bridge routes in the original graph. -/

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.leaf_transport_of_chain {c d : TriangleChain G}
    (hc : c.Feasible) (hd : d.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s a : Finset V}
    (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (ha' : a ∈ d.blocks)
    (z : V) (hz : z ∈ s) (ht : d.terminal = z) (hT : d.triangle = p.triangle)
    (hlink : degreeIn G z {p.vertices 2, p.vertices 3} = 1)
    (hweight : 11 ≤ contacts G (insert z p.support) a) :
    degreeIn G p.leaf a = 0 ∧ degreeIn G z a = 0 ∧ 11 ≤ contacts G p.triangle a := by
  have hFQ : Disjoint p.support s := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hne : p.leaf ≠ d.terminal := by
    rw [ht]
    intro he
    exact disjoint_left.mp hFQ (p.support_eq ▸ mem_insert_self _ _) (he.symm ▸ hz)
  have hpos : 0 < degreeIn G z {p.vertices 2, p.vertices 3} := by omega
  obtain ⟨u, hu⟩ := card_pos.mp hpos
  obtain ⟨hu, hadj⟩ := mem_filter.mp hu
  have hadj' : G.Adj d.terminal (p.vertices 2) ∨ G.Adj d.terminal (p.vertices 3) := by
    rw [ht]
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact Or.inl hadj
    · exact Or.inr hadj
  have hcon := hc.two_exposed_leaves hd hcard hdeg hn p hp hT hadj' hne ha ha'
    (by rw [ht]; exact hweight)
  rwa [ht] at hcon

theorem TriangleChain.Feasible.leaf_transport {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s a : Finset V}
    (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (z : V) (hz : z ∈ s) (hlink : degreeIn G z {p.vertices 2, p.vertices 3} = 1)
    (hweight : 11 ≤ contacts G (insert z p.support) a)
    (hroute :
      (QuadOn G (insert p.leaf (s.erase z)) ∧
        edgeCount G (insert p.leaf (s.erase z)) = edgeCount G s) ∨
      ∃ b ∈ c.blocks, b ≠ s ∧ b ≠ a ∧ ∃ y ∈ b,
        QuadOn G (insert p.leaf (b.erase y)) ∧
        edgeCount G (insert p.leaf (b.erase y)) = edgeCount G b ∧
        QuadOn G (insert y (s.erase z)) ∧
        edgeCount G (insert y (s.erase z)) = edgeCount G s) :
    degreeIn G p.leaf a = 0 ∧ degreeIn G z a = 0 ∧ 11 ≤ contacts G p.triangle a := by
  rcases hroute with ⟨hrep, hscore⟩ | ⟨b, hb, hbs, hba, y, hy, hrep, hscore, hrep', hscore'⟩
  · obtain ⟨d, hd, ht, hT, _, _, hkeep⟩ := TwoExposed.one_route hc p hp hs z hz hrep hscore
    exact hc.leaf_transport_of_chain hd hcard hdeg hn p hp hs ha (hkeep a ha has)
      z hz ht hT hlink hweight
  · obtain ⟨d, hd, ht, hT, _, _, hkeep⟩ := TwoExposed.two_route hc p hp hs hb hbs z y hz hy
      hrep hscore hrep' hscore'
    exact hc.leaf_transport_of_chain hd hcard hdeg hn p hp hs ha (hkeep a ha has hba.symm)
      z hz ht hT hlink hweight

end Erdos577
