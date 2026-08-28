import ErdosProblems.Erdos577.JointLeafSmallHigh

/-! The full small-third-degree case of TeX9.48, including the two zero leaf rows. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem small_third_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseOne p q ∨ CaseTwo p q)
    (hweight : 13 ≤ sixWeight p q a) (hsmall : degreeIn G (p.vertices 3) a ≤ 2) : False := by
  have hx2 : degreeIn G p.leaf a ≤ 2 := by
    by_contra! hh
    exact small_third_high_leaf_false hc hcard hn p hp hs ha has q hq hcase hweight hsmall
      (Or.inl (by omega))
  have ht2 : degreeIn G (q 3) a ≤ 2 := by
    by_contra! hh
    exact small_third_high_leaf_false hc hcard hn p hp hs ha has q hq hcase hweight hsmall
      (Or.inr (by omega))
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hQA : Disjoint q.support a := by rw [hq]; exact c.property.blocks_disjoint hs ha has.symm
  obtain ⟨d, hd, _, _, hp', _, _, _, hkeep⟩ :=
    exists_exposed_chain hc hcard hn p hp hs q hq hFQ hcase
  let p' := exposedPaw p q hFQ hcase
  have had := hkeep a ha has
  have htri' : p'.triangle = p.triangle := exposedPaw_triangle p q hFQ hcase
  have htout : q 3 ∉ p.support ∪ a := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp hFQ hh ((q.mem_support _).mpr ⟨3, rfl⟩)
    · exact disjoint_left.mp hQA ((q.mem_support _).mpr ⟨3, rfl⟩) hh
  have hw := hweight
  unfold sixWeight at hw
  have hheavy : 9 ≤ contacts G p.support a := by omega
  have hxzero : degreeIn G p.leaf a = 0 := by
    by_contra hnonzero
    have hpos : 0 < degreeIn G p.leaf a := Nat.pos_of_ne_zero hnonzero
    have hcounts := heavy_positive_counts hc hcard hdeg hn p hp ha hheavy hpos
    have htdegree : 2 ≤ degreeIn G (q 3) a := by omega
    have hf := heavy_positive_outside_factor hc hcard hdeg hn p hp ha hheavy hpos
      (q 3) htout htdegree
    apply d.no_local_factor hcard hn had
    rw [← hp', exposedPaw_support, insert_union]
    exact hf
  have hacard : a.card = 4 := (c.property.blocks_quad a ha).card
  have hrbound := degreeIn_le_card G p.center a
  have hbbound := degreeIn_le_card G (p.vertices 2) a
  rw [hacard] at hrbound hbbound
  have hold := p.contacts_support a
  have hT := p.contacts_triangle a
  change contacts G p.triangle a = degreeIn G p.center a +
    (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at hT
  have htpos : 0 < degreeIn G (q 3) a := by omega
  have hnew : contacts G p'.support a = degreeIn G (q 3) a + contacts G p.triangle a := by
    rw [p'.contacts_support, htri']
    rfl
  have hnew9 := positive_contacts_le_nine hd.toFeasible hcard hdeg hn p' hp' had htpos
  omega

end Erdos577.JointClaims
