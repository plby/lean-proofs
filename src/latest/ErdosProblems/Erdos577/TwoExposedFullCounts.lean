import ErdosProblems.Erdos577.TwoExposedBounds

/-! Exact degree consequences for a full first leaf and a large second leaf. -/

namespace Erdos577.TwoExposed

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem PawPair.full_zero_counts {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) {p p' : Paw G} (h : PawPair p p')
    (hp : p.support = c.remainder) (hp' : p'.support = d.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (ha' : a ∈ d.blocks)
    (hweight : 11 ≤ contacts G (insert p'.leaf p.support) a)
    (hx : degreeIn G p.leaf a = 4) (hz : 3 ≤ degreeIn G p'.leaf a)
    (hthird : degreeIn G (p.vertices 3) a = 0) :
    degreeIn G (p.vertices 2) a = 1 ∧ degreeIn G p'.leaf a = 3 ∧
      degreeIn G p.center a = 3 := by
  have hfirst := large_leaf_weighted_le_six hc hcard hdeg hn p hp ha (by omega)
  have hsecond := large_leaf_weighted_le_six hd hcard hdeg hn p' hp' ha' hz
  rw [h.second, h.third] at hsecond
  have hw := hweight
  rw [h.five_contacts, p.contacts_triangle] at hw
  change 11 ≤ degreeIn G p.leaf a + degreeIn G p'.leaf a +
    (degreeIn G p.center a + (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a)) at hw
  have hzcap := degreeIn_le_card G p'.leaf a
  rw [(c.property.blocks_quad a ha).card] at hzcap
  have hrpos : 0 < degreeIn G p.center a := by omega
  have hbsmall := (hc.claim_two_three hcard hdeg hn p hp ha hx hrpos).1
  have hbone : degreeIn G (p.vertices 2) a = 1 := by omega
  have hr2 : 2 ≤ degreeIn G p.center a := by omega
  have hznot : degreeIn G p'.leaf a ≠ 4 := by
    intro hz4
    have hbpos : 0 < degreeIn G p'.center a := by rw [h.center, hbone]; decide
    have hrsmall := (hd.claim_two_three hcard hdeg hn p' hp' ha' hz4 hbpos).1
    rw [h.second] at hrsmall
    omega
  exact ⟨hbone, by omega, by omega⟩

theorem PawPair.full_positive_counts {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) {p p' : Paw G} (h : PawPair p p')
    (hp : p.support = c.remainder) (hp' : p'.support = d.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (ha' : a ∈ d.blocks)
    (hweight : 11 ≤ contacts G (insert p'.leaf p.support) a)
    (hx : degreeIn G p.leaf a = 4) (hz : 3 ≤ degreeIn G p'.leaf a)
    (hthird : 0 < degreeIn G (p.vertices 3) a) :
    degreeIn G (p.vertices 2) a = 1 ∧ degreeIn G (p.vertices 3) a = 1 ∧
      0 < degreeIn G p.center a := by
  have hfirst := large_leaf_weighted_le_six hc hcard hdeg hn p hp ha (by omega)
  have hsecond := large_leaf_weighted_le_six hd hcard hdeg hn p' hp' ha' hz
  rw [h.second, h.third] at hsecond
  have hw := hweight
  rw [h.five_contacts, p.contacts_triangle] at hw
  change 11 ≤ degreeIn G p.leaf a + degreeIn G p'.leaf a +
    (degreeIn G p.center a + (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a)) at hw
  have hzcap := degreeIn_le_card G p'.leaf a
  rw [(c.property.blocks_quad a ha).card] at hzcap
  exact ⟨by omega, by omega, by omega⟩

end Erdos577.TwoExposed
