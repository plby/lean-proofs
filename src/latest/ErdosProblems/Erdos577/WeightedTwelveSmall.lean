import ErdosProblems.Erdos577.WeightedTwelveFull

/-! The actual swap applies the full-row obstruction in either terminal direction. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem terminal_degrees_le_two {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (h : WeightedPawBlock.Pattern12 p q)
    (hweight : 11 ≤ contacts G (five p q) a) :
    degreeIn G p.leaf a ≤ 2 ∧ degreeIn G (q 3) a ≤ 2 := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  obtain ⟨e, he, _, _, hp', hq', _, _, _, hpat', hkeep⟩ :=
    exists_swap hc hcard hn p hp hs q hq hd h
  let p' := exposedPaw p q hd h
  let q' := exposedQuad p q hd h
  have ha' := hkeep a ha has
  have hweight' : 11 ≤ contacts G (five p' q') a := by
    rw [five_swap_eq]
    exact hweight
  have hnX : degreeIn G p.leaf a ≠ 4 :=
    fun hh ↦ full_leaf_false hc hcard hdeg hn p hp hs ha has q hq h hweight hh
  have hnY : degreeIn G (q 3) a ≠ 4 := fun hh ↦
    full_leaf_false he.toFeasible hcard hdeg hn p' hp' hq' ha'.1 ha'.2 q' rfl hpat' hweight' hh
  have hxcap := degreeIn_le_card G p.leaf a
  have hycap := degreeIn_le_card G (q 3) a
  rw [(c.property.blocks_quad a ha).card] at hxcap hycap
  have hw := hweight
  rw [(five_data p q hd).2, p.contacts_support] at hw
  have impossible (hT : contacts G p.triangle a ≤ 4) : False := by omega
  constructor
  · by_contra hlarge
    exact impossible (JointClaims.triangle_contacts_le_four hc hcard hn p hp ha (by omega))
  · by_contra hlarge
    have hT := JointClaims.triangle_contacts_le_four he.toFeasible hcard hn p' hp' ha'.1 (by
      change 3 ≤ degreeIn G (q 3) a
      omega)
    rw [exposedPaw_triangle] at hT
    exact impossible hT

end Erdos577.WeightedTwelve
