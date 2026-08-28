import ErdosProblems.Erdos577.TwoExposedPositiveFactor

/-! TeX9.67: two actual chains with different centers force both heavy exposed leaves to vanish. -/

namespace Erdos577.TwoExposed

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem PawPair.full_false {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) {p p' : Paw G} (h : PawPair p p')
    (hp : p.support = c.remainder) (hp' : p'.support = d.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (ha' : a ∈ d.blocks)
    (hweight : 11 ≤ contacts G (insert p'.leaf p.support) a)
    (hx : degreeIn G p.leaf a = 4) (hz : 3 ≤ degreeIn G p'.leaf a) : False := by
  by_cases ht : degreeIn G (p.vertices 3) a = 0
  · obtain ⟨hb, _, hr⟩ := h.full_zero_counts hc hd hcard hdeg hn hp hp' ha ha' hweight hx hz ht
    exact full_center_three_second_one_false hc hcard hdeg hn p hp ha hx hr hb
  · obtain ⟨hb, ht', hr⟩ := h.full_positive_counts hc hd hcard hdeg hn hp hp' ha ha' hweight
      hx hz (by omega)
    exact full_three_positive_false hc hcard hn p hp ha hx hr (by omega) (by omega)

theorem PawPair.dense {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) {p p' : Paw G} (h : PawPair p p')
    (hp : p.support = c.remainder) (hp' : p'.support = d.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (ha' : a ∈ d.blocks)
    (hweight : 11 ≤ contacts G (insert p'.leaf p.support) a) :
    degreeIn G p.leaf a = 0 ∧ degreeIn G p'.leaf a = 0 ∧ 11 ≤ contacts G p.triangle a := by
  by_cases hz : degreeIn G p'.leaf a = 0
  · obtain ⟨hx, hT⟩ := h.zero_other_dense hc hcard hdeg hn hp ha hweight hz
    exact ⟨hx, hz, hT⟩
  · by_cases hx : degreeIn G p.leaf a = 0
    · obtain ⟨hz', hT⟩ := h.symm.zero_other_dense hd hcard hdeg hn hp' ha'
        (by rw [h.five_symm]; exact hweight) hx
      rw [h.triangle] at hT
      exact ⟨hx, hz', hT⟩
    · obtain ⟨hx3, hz3, hfull, _, _⟩ := h.both_positive_large hc hd hcard hdeg hn
        hp hp' ha ha' hweight (by omega) (by omega)
      rcases hfull with hx4 | hz4
      · exact False.elim (h.full_false hc hd hcard hdeg hn hp hp' ha ha' hweight hx4 hz3)
      · exact False.elim (h.symm.full_false hd hc hcard hdeg hn hp' hp ha' ha
          (by rw [h.five_symm]; exact hweight) hz4 hx3)

end Erdos577.TwoExposed

namespace Erdos577

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem TriangleChain.Feasible.two_exposed_leaves_at_second {c d : TriangleChain G}
    (hc : c.Feasible) (hd : d.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (htri : d.triangle = p.triangle)
    (hadj : G.Adj d.terminal (p.vertices 2)) (hne : p.leaf ≠ d.terminal)
    {a : Finset V} (ha : a ∈ c.blocks) (ha' : a ∈ d.blocks)
    (hweight : 11 ≤ contacts G (insert d.terminal p.support) a) :
    degreeIn G p.leaf a = 0 ∧ degreeIn G d.terminal a = 0 ∧
      11 ≤ contacts G p.triangle a := by
  have hz : d.terminal ∉ p.triangle := by rw [← htri]; exact d.property.terminal_not_mem
  let p' := TwoExposed.alternatePaw p d.terminal hz hadj
  have hpair := TwoExposed.alternatePaw_pair p d.terminal hz hadj hne
  have hp' : p'.support = d.remainder := by
    change p'.support = insert d.terminal d.triangle
    rw [p'.support_eq, hpair.triangle, htri]
    rfl
  exact hpair.dense hc hd hcard hdeg hn hp hp' ha ha' hweight

theorem TriangleChain.Feasible.two_exposed_leaves {c d : TriangleChain G}
    (hc : c.Feasible) (hd : d.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (htri : d.triangle = p.triangle)
    (hadj : G.Adj d.terminal (p.vertices 2) ∨ G.Adj d.terminal (p.vertices 3))
    (hne : p.leaf ≠ d.terminal) {a : Finset V} (ha : a ∈ c.blocks) (ha' : a ∈ d.blocks)
    (hweight : 11 ≤ contacts G (insert d.terminal p.support) a) :
    degreeIn G p.leaf a = 0 ∧ degreeIn G d.terminal a = 0 ∧
      11 ≤ contacts G p.triangle a := by
  rcases hadj with hadj | hadj
  · exact hc.two_exposed_leaves_at_second hd hcard hdeg hn p hp htri hadj hne ha ha' hweight
  · have hnew := hc.two_exposed_leaves_at_second hd hcard hdeg hn p.swapNoncentral
      (by rw [Paw.swapNoncentral_support, hp])
      (by rw [Paw.swapNoncentral_triangle]; exact htri)
      (by exact hadj) (by exact hne) ha ha'
      (by rw [Paw.swapNoncentral_support]; exact hweight)
    simpa only [Paw.swapNoncentral_leaf, Paw.swapNoncentral_triangle] using hnew

end Erdos577
