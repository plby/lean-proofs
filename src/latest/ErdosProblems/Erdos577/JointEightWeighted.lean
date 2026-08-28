import ErdosProblems.Erdos577.JointEightTerminal

/-! The high weighted triple has its high noncentral row at the original center. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem large_weighted_patterns {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (hthree : 3 ≤ degreeIn G p.leaf a)
    (hhigh : 7 ≤ degreeIn G p.leaf a + degreeIn G (p.vertices 2) a +
      degreeIn G (p.vertices 3) a) :
    ∃ swap : Bool, ∃ v : Quadrilateral G, v.support = a ∧
      (WeightedPawBlock.Pattern10 (FirstPaw.normalizedPaw p swap) v ∨
       WeightedPawBlock.Pattern11 (FirstPaw.normalizedPaw p swap) v ∨
       WeightedPawBlock.Pattern12 (FirstPaw.normalizedPaw p swap) v) := by
  obtain ⟨v, hv⟩ := c.property.blocks_quad a ha
  obtain ⟨swap, v', hv', hpat⟩ := hc.weighted_paw_classification hcard hdeg hn p hp ha v hv
    (by rw [hv]; exact hhigh) (by rw [hv]; omega)
  have hva : v'.support = a := hv'.trans hv
  have hp' : (FirstPaw.normalizedPaw p swap).support = c.remainder := by
    rw [FirstPaw.normalizedPaw_support, hp]
  refine ⟨swap, v', hva, ?_⟩
  rcases hpat with h | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | h | h
  · have hh := h.1
    change degreeIn G (FirstPaw.normalizedPaw p swap).leaf v'.support = 1 at hh
    rw [FirstPaw.normalizedPaw_leaf, hva] at hh
    omega
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact False.elim (hc.not_weighted_pattern13 hcard hdeg hn _ hp' ha v' hva h)
  · exact False.elim (hc.not_weighted_pattern14 hcard hdeg hn _ hp' ha v' hva h)

theorem eight_high_patterns {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseTwo p q)
    (hweight : 17 ≤ eightWeight p q a)
    (hpos : 0 < degreeIn G p.leaf a + degreeIn G (q 3) a)
    (hhigh : 7 ≤ degreeIn G (q 3) a + degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hFQ : Disjoint p.support q.support) :
    ∃ v : Quadrilateral G, v.support = a ∧
      (WeightedPawBlock.Pattern10 (exposedPaw p q hFQ (Or.inr hcase)) v ∨
       WeightedPawBlock.Pattern11 (exposedPaw p q hFQ (Or.inr hcase)) v ∨
       WeightedPawBlock.Pattern12 (exposedPaw p q hFQ (Or.inr hcase)) v) := by
  have ht3 := eight_high_terminal hc hcard hdeg hn p hp hs ha has q hq hcase hweight hpos hhigh
  obtain ⟨_, hT4, _, hxc4⟩ := eight_terminal_rows hc hcard hn p hp hs ha has q hq hcase ht3
  obtain ⟨d, hd, _, _, hp', _, _, _, hkeep⟩ :=
    exists_exposed_chain hc hcard hn p hp hs q hq hFQ (Or.inr hcase)
  let p' := exposedPaw p q hFQ (Or.inr hcase)
  obtain ⟨swap, v, hv, hpat⟩ := large_weighted_patterns hd.toFeasible hcard hdeg hn
    p' hp' (hkeep a ha has) ht3 hhigh
  have hswap : swap = false := by
    cases swap
    · rfl
    · obtain ⟨_, _, hlow⟩ := good_weighted_counts (FirstPaw.normalizedPaw p' true) v hpat
      change degreeIn G (q 3) v.support + degreeIn G p.center v.support ≤ 4 at hlow
      rw [hv] at hlow
      have ht4 := degreeIn_le_card G (q 3) a
      rw [(c.property.blocks_quad a ha).card] at ht4
      have he := p.contacts_triangle a
      change contacts G p.triangle a = degreeIn G p.center a +
        (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at he
      rw [eightWeight_eq_rows] at hweight
      omega
  subst swap
  exact ⟨v, hv, hpat⟩

end Erdos577.JointClaims
