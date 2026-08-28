import ErdosProblems.Erdos577.JointEightCount
import ErdosProblems.Erdos577.SmallLeafClassification

/-! A positive pair of exposed leaves forces the second terminal row to have degree at least three.
-/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem eight_high_terminal {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseTwo p q)
    (hweight : 17 ≤ eightWeight p q a)
    (hpos : 0 < degreeIn G p.leaf a + degreeIn G (q 3) a)
    (hhigh : 7 ≤ degreeIn G (q 3) a + degreeIn G p.center a + degreeIn G (p.vertices 3) a) :
    3 ≤ degreeIn G (q 3) a := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  obtain ⟨d, hd, _, _, hp', _, _, _, hkeep⟩ :=
    exists_exposed_chain hc hcard hn p hp hs q hq hFQ (Or.inr hcase)
  let p' := exposedPaw p q hFQ (Or.inr hcase)
  have had := hkeep a ha has
  obtain ⟨v, hv⟩ := c.property.blocks_quad a ha
  by_contra! hsmall
  have hsmall' : degreeIn G p'.leaf v.support ≤ 2 := by rw [hv]; exact Nat.le_of_lt_succ hsmall
  have hsum := hd.toFeasible.small_leaf_weight_le_eight hcard hdeg hn p' hp' had v hv hsmall'
  change 2 * degreeIn G (q 3) v.support + degreeIn G p.center v.support +
    degreeIn G (p.vertices 3) v.support ≤ 8 at hsum
  rw [hv] at hsum
  have hc3 : 3 ≤ degreeIn G (p.vertices 3) a := by
    by_cases ht0 : degreeIn G (q 3) a = 0
    · have hr4 := degreeIn_le_card G p.center a
      rw [(c.property.blocks_quad a ha).card] at hr4
      omega
    · obtain ⟨v', hv', hpat⟩ := hd.toFeasible.small_leaf_pattern_nine hcard hdeg hn
        p' hp' had v hv hsmall' (by rw [hv]; exact Nat.pos_of_ne_zero ht0)
        (by rw [hv]; exact hhigh)
      have hh := hpat.2.2.degree p' v' 3 14
      have h14 : (∑ j : Fin 4, ((14 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
      rw [h14, hv', hv] at hh
      exact hh.ge
  have hF := p.contacts_support a
  have hT := p.contacts_triangle a
  change contacts G p.triangle a = degreeIn G p.center a +
    (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at hT
  rw [eightWeight_eq_rows] at hweight
  have hF9 : 9 ≤ contacts G p.support a := by omega
  have hx0 : degreeIn G p.leaf a = 0 := by
    by_contra hh
    have he := (heavy_positive_counts hc hcard hdeg hn p hp ha hF9
      (Nat.pos_of_ne_zero hh)).2.2.2
    omega
  have htpos : 0 < degreeIn G p'.leaf a := by change 0 < degreeIn G (q 3) a; omega
  have hnew9 := positive_contacts_le_nine hd.toFeasible hcard hdeg hn p' hp' had htpos
  have hnew : contacts G p'.support a = degreeIn G (q 3) a + contacts G p.triangle a := by
    rw [p'.contacts_support, exposedPaw_triangle]
    rfl
  omega

theorem eight_terminal_rows {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseTwo p q)
    (hthree : 3 ≤ degreeIn G (q 3) a) :
    (∀ u ∈ a, QuadOn G (insert (q 3) (a.erase u))) ∧ contacts G p.triangle a ≤ 4 ∧
      Disjoint (a.filter (G.Adj p.leaf)) (a.filter (G.Adj (p.vertices 3))) ∧
      degreeIn G p.leaf a + degreeIn G (p.vertices 3) a ≤ 4 := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  obtain ⟨d, hd, _, _, hp', _, _, _, hkeep⟩ :=
    exists_exposed_chain hc hcard hn p hp hs q hq hFQ (Or.inr hcase)
  let p' := exposedPaw p q hFQ (Or.inr hcase)
  have had := hkeep a ha has
  have hrep (u : V) (hu : u ∈ a) : QuadOn G (insert (q 3) (a.erase u)) :=
    (hd.toFeasible.presentPaw_feasible p' hp').terminal_universal_replace had hthree hu
  have hT := triangle_contacts_le_four hd.toFeasible hcard hn p' hp' had hthree
  rw [exposedPaw_triangle] at hT
  have hdis : Disjoint (a.filter (G.Adj p.leaf)) (a.filter (G.Adj (p.vertices 3))) := by
    apply disjoint_left.mpr
    intro u hu hv
    obtain ⟨hua, hxu⟩ := mem_filter.mp hu
    exact common_third_first_factor hcard hn p hp hs ha has q hq
      ⟨u, hua, hxu, (mem_filter.mp hv).2, hrep u hua⟩
      (case_two_universal hc p hp hs q hq hcase (q 3) ((q.mem_support _).mpr ⟨3, rfl⟩))
  refine ⟨hrep, hT, hdis, ?_⟩
  have hh := card_le_card (union_subset (filter_subset (G.Adj p.leaf) a)
    (filter_subset (G.Adj (p.vertices 3)) a))
  rw [card_union_of_disjoint hdis, (c.property.blocks_quad a ha).card] at hh
  exact hh

end Erdos577.JointClaims
