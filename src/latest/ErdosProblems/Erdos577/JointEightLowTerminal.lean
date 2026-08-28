import ErdosProblems.Erdos577.JointEightTerminal

/-! The low weighted triple also gives a large terminal row and a complete selected block. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem eight_low_terminal {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseTwo p q)
    (hweight : 17 ≤ eightWeight p q a)
    (hpos : 0 < degreeIn G p.leaf a + degreeIn G (q 3) a)
    (hlow : degreeIn G (q 3) a + degreeIn G p.center a + degreeIn G (p.vertices 3) a ≤ 6) :
    contacts G p.support a ≤ 8 ∧ 3 ≤ degreeIn G (q 3) a ∧
      7 ≤ degreeIn G p.leaf a + degreeIn G (q 3) a ∧
      3 ≤ contacts G p.triangle a ∧ G.IsNClique 4 a := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hQA : Disjoint q.support a := by rw [hq]; exact c.property.blocks_disjoint hs ha has.symm
  obtain ⟨d, hd, _, _, hp', _, _, _, hkeep⟩ :=
    exists_exposed_chain hc hcard hn p hp hs q hq hFQ (Or.inr hcase)
  let p' := exposedPaw p q hFQ (Or.inr hcase)
  have had := hkeep a ha has
  have hF := p.contacts_support a
  have hT := p.contacts_triangle a
  change contacts G p.triangle a = degreeIn G p.center a +
    (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at hT
  have hw := hweight
  rw [eightWeight_eq_rows] at hw
  have hsum : 11 ≤ contacts G p.support a + degreeIn G (q 3) a := by omega
  have hbound : contacts G p.support a ≤ 8 := by
    by_contra! hh
    have hx0 : degreeIn G p.leaf a = 0 := by
      by_contra hx
      have hnine := (heavy_positive_counts hc hcard hdeg hn p hp ha
        (by omega) (Nat.pos_of_ne_zero hx)).2.1
      have ht2 : 2 ≤ degreeIn G (q 3) a := by omega
      have htout : q 3 ∉ p.support ∪ a := by
        intro ht
        rcases mem_union.mp ht with ht | ht
        · exact disjoint_left.mp hFQ ht ((q.mem_support _).mpr ⟨3, rfl⟩)
        · exact disjoint_left.mp hQA ((q.mem_support _).mpr ⟨3, rfl⟩) ht
      have hf := heavy_positive_outside_factor hc hcard hdeg hn p hp ha
        (by omega) (Nat.pos_of_ne_zero hx) (q 3) htout ht2
      exact hn ((c.presentPaw p hp).hasPacking_of_core_replacement hcard hs ha has.symm
        (hq ▸ (q.mem_support _).mpr ⟨3, rfl⟩) hf
        ((hc.presentPaw_feasible p hp).terminal_universal_replace hs
          (hq ▸ leaf_lower p q (Or.inr hcase)) (hq ▸ (q.mem_support _).mpr ⟨3, rfl⟩)))
    have htpos : 0 < degreeIn G p'.leaf a := by change 0 < degreeIn G (q 3) a; omega
    have hnew9 := positive_contacts_le_nine hd.toFeasible hcard hdeg hn p' hp' had htpos
    have hnew : contacts G p'.support a = degreeIn G (q 3) a + contacts G p.triangle a := by
      rw [p'.contacts_support, exposedPaw_triangle]
      rfl
    omega
  have ht3 : 3 ≤ degreeIn G (q 3) a := by omega
  have hT4 := (eight_terminal_rows hc hcard hn p hp hs ha has q hq hcase ht3).2.1
  have hx4 := degreeIn_le_card G p.leaf a
  have ht4 := degreeIn_le_card G (q 3) a
  rw [(c.property.blocks_quad a ha).card] at hx4 ht4
  refine ⟨hbound, ht3, by omega, by omega, ?_⟩
  by_cases hxfull : degreeIn G p.leaf a = 4
  · exact FullRow.full_leaf_clique hc p hp ha hxfull
  · exact FullRow.full_leaf_clique hd.toFeasible p' hp' had
      (show degreeIn G (q 3) a = 4 by omega)

end Erdos577.JointClaims
