import ErdosProblems.Erdos577.JointLeafCounts

/-! Paired paw contact bounds in the large third-row case. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem contacts_le_eight_with_other_leaf {c d : TriangleChain G}
    (hc : c.Feasible) (hd : d.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p p' : Paw G) (hp : p.support = c.remainder) (hp' : p'.support = d.remainder)
    (htri : p'.triangle = p.triangle) {a : Finset V} (ha : a ∈ c.blocks) (ha' : a ∈ d.blocks)
    (hlarge : 3 ≤ degreeIn G (p.vertices 3) a)
    (hpos : 0 < degreeIn G p.leaf a + degreeIn G p'.leaf a) :
    contacts G p.support a ≤ 8 := by
  by_contra! hheavy
  have hxzero : degreeIn G p.leaf a = 0 := by
    by_contra hnzero
    have hh := positive_leaf_third_large hc hcard hdeg hn p hp ha
      (Nat.pos_of_ne_zero hnzero) hlarge
    omega
  have hotherpos : 0 < degreeIn G p'.leaf a := by omega
  have hother := positive_contacts_le_nine hd hcard hdeg hn p' hp' ha' hotherpos
  have hold := p.contacts_support a
  have hnew := p'.contacts_support a
  rw [htri] at hnew
  omega

theorem paired_contacts_le_eight {c d : TriangleChain G}
    (hc : c.Feasible) (hd : d.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p p' : Paw G) (hp : p.support = c.remainder) (hp' : p'.support = d.remainder)
    (htri : p'.triangle = p.triangle) {a : Finset V} (ha : a ∈ c.blocks) (ha' : a ∈ d.blocks)
    (hlarge : 3 ≤ degreeIn G (p.vertices 3) a) (hlarge' : 3 ≤ degreeIn G (p'.vertices 3) a)
    (hpos : 0 < degreeIn G p.leaf a + degreeIn G p'.leaf a) :
    contacts G p.support a ≤ 8 ∧ contacts G p'.support a ≤ 8 := by
  exact ⟨contacts_le_eight_with_other_leaf hc hd hcard hdeg hn p p' hp hp' htri ha ha' hlarge hpos,
    contacts_le_eight_with_other_leaf hd hc hcard hdeg hn p' p hp' hp htri.symm ha' ha
      hlarge' (by omega)⟩

end Erdos577.JointClaims
