import ErdosProblems.Erdos577.TwoExposedPaws

/-! Claim2.2 transfers its factor through the other actual chain; both positive leaves are large. -/

namespace Erdos577.TwoExposed

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem large_leaf_weighted_le_six {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (hthree : 3 ≤ degreeIn G p.leaf a) :
    degreeIn G p.leaf a + degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a ≤ 6 := by
  by_contra hlarge
  have hsmall := hc.heavy_weighted_leaf_le_two hcard hdeg hn p hp ha (by omega)
  omega

theorem PawPair.heavy_other_false {c d : TriangleChain G} (hd : d.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) {p p' : Paw G} (h : PawPair p p')
    (hp : p.support = c.remainder) (hp' : p'.support = d.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (ha' : a ∈ d.blocks)
    (hweight : 11 ≤ contacts G (insert p'.leaf p.support) a)
    (hpos : 0 < degreeIn G p'.leaf a) (hheavy : 9 ≤ contacts G p'.support a) : False := by
  have hexact := (JointClaims.heavy_positive_counts hd hcard hdeg hn p' hp' ha' hheavy hpos).2.1
  have hsum := p'.contacts_support a
  rw [h.triangle] at hsum
  have hw := hweight
  rw [h.five_contacts] at hw
  have hx2 : 2 ≤ degreeIn G p.leaf a := by omega
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hxout : p.leaf ∉ p'.support ∪ a := by
    simp only [mem_union, not_or]
    exact ⟨h.symm.other_leaf_out,
      fun hh ↦ disjoint_left.mp hFA (p.support_eq ▸ mem_insert_self _ _) hh⟩
  have hf := JointClaims.heavy_positive_outside_factor hd hcard hdeg hn p' hp' ha'
    hheavy hpos p.leaf hxout hx2
  apply c.no_local_factor hcard hn ha
  rw [← hp, p.support_eq, insert_union, ← h.triangle]
  exact hf

theorem PawPair.zero_other_dense {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p p' : Paw G} (h : PawPair p p') (hp : p.support = c.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (hweight : 11 ≤ contacts G (insert p'.leaf p.support) a)
    (hz : degreeIn G p'.leaf a = 0) :
    degreeIn G p.leaf a = 0 ∧ 11 ≤ contacts G p.triangle a := by
  have hw := hweight
  rw [h.five_contacts, hz, add_zero] at hw
  have hx : degreeIn G p.leaf a = 0 := by
    by_contra hpos
    have hbound := JointClaims.positive_contacts_le_nine hc hcard hdeg hn p hp ha (by omega)
    rw [p.contacts_support] at hbound
    omega
  exact ⟨hx, by omega⟩

theorem PawPair.both_positive_large {c d : TriangleChain G} (hc : c.Feasible) (hd : d.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) {p p' : Paw G} (h : PawPair p p')
    (hp : p.support = c.remainder) (hp' : p'.support = d.remainder)
    {a : Finset V} (ha : a ∈ c.blocks) (ha' : a ∈ d.blocks)
    (hweight : 11 ≤ contacts G (insert p'.leaf p.support) a)
    (hxpos : 0 < degreeIn G p.leaf a) (hzpos : 0 < degreeIn G p'.leaf a) :
    3 ≤ degreeIn G p.leaf a ∧ 3 ≤ degreeIn G p'.leaf a ∧
      (degreeIn G p.leaf a = 4 ∨ degreeIn G p'.leaf a = 4) ∧
      3 ≤ contacts G p.triangle a ∧ contacts G p.triangle a ≤ 4 := by
  have hother : contacts G p'.support a ≤ 8 := by
    by_contra hlarge
    exact h.heavy_other_false hd hcard hdeg hn hp hp' ha ha' hweight hzpos (by omega)
  have hold : contacts G p.support a ≤ 8 := by
    by_contra hlarge
    exact h.symm.heavy_other_false hc hcard hdeg hn hp' hp ha' ha
      (by rw [h.five_symm]; exact hweight) hxpos (by omega)
  have hsum := p.contacts_support a
  have hsum' := p'.contacts_support a
  rw [h.triangle] at hsum'
  have hw := hweight
  rw [h.five_contacts] at hw
  have hx3 : 3 ≤ degreeIn G p.leaf a := by omega
  have hz3 : 3 ≤ degreeIn G p'.leaf a := by omega
  have hT := JointClaims.triangle_contacts_le_four hc hcard hn p hp ha hx3
  have hxcap := degreeIn_le_card G p.leaf a
  have hzcap := degreeIn_le_card G p'.leaf a
  rw [(c.property.blocks_quad a ha).card] at hxcap hzcap
  exact ⟨hx3, hz3, by omega, by omega, hT⟩

end Erdos577.TwoExposed
