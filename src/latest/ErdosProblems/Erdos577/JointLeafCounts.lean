import ErdosProblems.Erdos577.JointSetup

/-! Numerical consequences of Claim2.2 for either of the two actual exposed paws. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem heavy_positive_counts {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (hheavy : 9 ≤ contacts G p.support a) (hleaf : 0 < degreeIn G p.leaf a) :
    degreeIn G p.leaf a = 1 ∧ contacts G p.support a = 9 ∧
      degreeIn G (p.vertices 2) a = 2 ∧ degreeIn G (p.vertices 3) a = 2 := by
  obtain ⟨v, hv⟩ := c.property.blocks_quad a ha
  have hh : 9 ≤ contacts G p.support v.support := by rw [hv]; exact hheavy
  rcases hc.claim_two_two hcard hdeg hn p hp ha v hv hh with hz | ⟨q, hq, hpat⟩
  · rw [hv] at hz
    omega
  have hqa : q.support = a := hq.trans hv
  obtain ⟨hx, hsum⟩ := PawBlock.surviving_counts p q (Or.inl hpat)
  have htwo := WeightedPawBlock.Row.degree p q 2 9 (hpat.2 2)
  have hthree := WeightedPawBlock.Row.degree p q 3 3 (hpat.2 3)
  have h9 : (∑ j : Fin 4, ((9 : ℕ).testBit j.val).toNat) = 2 := by decide +kernel
  have h3 : (∑ j : Fin 4, ((3 : ℕ).testBit j.val).toNat) = 2 := by decide +kernel
  rw [hqa] at hx hsum htwo hthree
  exact ⟨hx, hsum, htwo.trans h9, hthree.trans h3⟩

theorem positive_contacts_le_nine {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (hleaf : 0 < degreeIn G p.leaf a) : contacts G p.support a ≤ 9 := by
  obtain ⟨q, hq⟩ := c.property.blocks_quad a ha
  have hh := hc.positive_leaf_contacts_le_nine hcard hdeg hn p hp ha q hq (by rw [hq]; exact hleaf)
  rwa [hq] at hh

theorem heavy_positive_outside_factor {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (hheavy : 9 ≤ contacts G p.support a) (hleaf : 0 < degreeIn G p.leaf a)
    (z : V) (hz : z ∉ p.support ∪ a) (hzdegree : 2 ≤ degreeIn G z a) :
    LocalFactor G (insert z (p.triangle ∪ a)) := by
  obtain ⟨q, hq⟩ := c.property.blocks_quad a ha
  have hf := (hc.first_paw_final hcard hdeg hn p hp ha q hq
    (by rw [hq]; exact hheavy) (by rw [hq]; exact hleaf)).2.2.1 z
    (by rw [hq]; exact hz) (by rw [hq]; exact hzdegree)
  rwa [hq] at hf

theorem positive_leaf_third_large {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (hleaf : 0 < degreeIn G p.leaf a) (hthird : 3 ≤ degreeIn G (p.vertices 3) a) :
    contacts G p.support a ≤ 8 := by
  by_contra! hheavy
  have hh := (heavy_positive_counts hc hcard hdeg hn p hp ha (by omega) hleaf).2.2.2
  omega

end Erdos577.JointClaims
