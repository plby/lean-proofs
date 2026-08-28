import ErdosProblems.Erdos577.JointEightHighZero
import ErdosProblems.Erdos577.JointEightLowZero

/-! The complete eight-row alternative, TeX9.52, without any extra maximizing choice of block. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def EightAlternative (p : Paw G) (q : Quadrilateral G) (a : Finset V) : Prop :=
  (degreeIn G p.leaf a = 0 ∧ degreeIn G (q 3) a = 0 ∧
    ∃ η : Fin 2, degreeIn G p.center a + degreeIn G (p.vertices 3) a = 7 + η.val ∧
      10 - η.val ≤ contacts G p.triangle a) ∨
  (∃ η : Fin 2, degreeIn G (q 3) a + degreeIn G p.center a = 7 + η.val ∧
    3 - 2 * η.val ≤ degreeIn G p.leaf a ∧
    degreeIn G (p.vertices 2) a = 0 ∧ degreeIn G (p.vertices 3) a = 0) ∨
  (degreeIn G (q 3) a = 4 ∧ 3 ≤ degreeIn G p.leaf a ∧ 3 ≤ degreeIn G p.center a ∧
    degreeIn G (p.vertices 2) a = 0 ∧ degreeIn G (p.vertices 3) a = 0) ∨
  (degreeIn G p.leaf a = 4 ∧ degreeIn G (q 3) a = 3 ∧ 3 ≤ degreeIn G p.center a ∧
    degreeIn G p.center a + degreeIn G (p.vertices 2) a = 4 ∧ degreeIn G (p.vertices 3) a = 0)

variable [Fintype V]

theorem eight_high_alternative {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseTwo p q)
    (hweight : 17 ≤ eightWeight p q a)
    (hpos : 0 < degreeIn G p.leaf a + degreeIn G (q 3) a)
    (hhigh : 7 ≤ degreeIn G (q 3) a + degreeIn G p.center a + degreeIn G (p.vertices 3) a) :
    ∃ η : Fin 2, degreeIn G (q 3) a + degreeIn G p.center a = 7 + η.val ∧
      3 - 2 * η.val ≤ degreeIn G p.leaf a ∧
      degreeIn G (p.vertices 2) a = 0 ∧ degreeIn G (p.vertices 3) a = 0 := by
  obtain ⟨hb0, hc0⟩ := eight_high_zero hc hcard hdeg hn p hp hs ha has q hq hcase
    hweight hpos hhigh
  have ht4 := degreeIn_le_card G (q 3) a
  have hr4 := degreeIn_le_card G p.center a
  rw [(c.property.blocks_quad a ha).card] at ht4 hr4
  rw [eightWeight_eq_rows] at hweight
  by_cases he : degreeIn G (q 3) a + degreeIn G p.center a = 7
  · exact ⟨0, by simp; omega, by simp; omega, hb0, hc0⟩
  · exact ⟨1, by simp; omega, by simp; omega, hb0, hc0⟩

theorem eight_low_alternative {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseTwo p q)
    (hweight : 17 ≤ eightWeight p q a)
    (hpos : 0 < degreeIn G p.leaf a + degreeIn G (q 3) a)
    (hlow : degreeIn G (q 3) a + degreeIn G p.center a + degreeIn G (p.vertices 3) a ≤ 6) :
    (degreeIn G (q 3) a = 4 ∧ 3 ≤ degreeIn G p.leaf a ∧ 3 ≤ degreeIn G p.center a ∧
      degreeIn G (p.vertices 2) a = 0 ∧ degreeIn G (p.vertices 3) a = 0) ∨
    (degreeIn G p.leaf a = 4 ∧ degreeIn G (q 3) a = 3 ∧ 3 ≤ degreeIn G p.center a ∧
      degreeIn G p.center a + degreeIn G (p.vertices 2) a = 4 ∧
      degreeIn G (p.vertices 3) a = 0) := by
  have hc0 := eight_low_zero hc hcard hdeg hn p hp hs ha has q hq hcase hweight hpos hlow
  obtain ⟨_, ht3, hxt7, _, _⟩ := eight_low_terminal hc hcard hdeg hn p hp hs ha has q hq hcase
    hweight hpos hlow
  have hT4 := (eight_terminal_rows hc hcard hn p hp hs ha has q hq hcase ht3).2.1
  have hT := p.contacts_triangle a
  change contacts G p.triangle a = degreeIn G p.center a +
    (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at hT
  have hx4 := degreeIn_le_card G p.leaf a
  have ht4 := degreeIn_le_card G (q 3) a
  rw [(c.property.blocks_quad a ha).card] at hx4 ht4
  rw [eightWeight_eq_rows] at hweight
  by_cases htfull : degreeIn G (q 3) a = 4
  · have hrpos : 0 < degreeIn G p.center a := by omega
    have hb0 : degreeIn G (p.vertices 2) a = 0 := by
      by_contra hh
      have hFQ : Disjoint p.support q.support := by
        rw [hp, hq]
        exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
      obtain ⟨d, hd, _, _, hp', _, _, _, hkeep⟩ :=
        exists_exposed_chain hc hcard hn p hp hs q hq hFQ (Or.inr hcase)
      have hr1 := (hd.toFeasible.claim_two_three hcard hdeg hn
        (exposedPaw p q hFQ (Or.inr hcase)) hp' (hkeep a ha has)
        htfull (Nat.pos_of_ne_zero hh)).1
      change degreeIn G p.center a ≤ 1 at hr1
      by_cases hxfull : degreeIn G p.leaf a = 4
      · have hb1 := (hc.claim_two_three hcard hdeg hn p hp ha hxfull hrpos).1
        omega
      · omega
    exact Or.inl ⟨htfull, by omega, by omega, hb0, hc0⟩
  · exact Or.inr ⟨by omega, by omega, by omega, by omega, hc0⟩

theorem every_eight_heavy_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseTwo p q)
    (hweight : 17 ≤ eightWeight p q a) : EightAlternative p q a := by
  by_cases hpos : 0 < degreeIn G p.leaf a + degreeIn G (q 3) a
  · apply Or.inr
    by_cases hhigh : 7 ≤ degreeIn G (q 3) a + degreeIn G p.center a +
        degreeIn G (p.vertices 3) a
    · exact Or.inl (eight_high_alternative hc hcard hdeg hn p hp hs ha has q hq hcase
        hweight hpos hhigh)
    · exact Or.inr (eight_low_alternative hc hcard hdeg hn p hp hs ha has q hq hcase
        hweight hpos (by omega))
  · apply Or.inl
    have hx0 : degreeIn G p.leaf a = 0 := by omega
    have ht0 : degreeIn G (q 3) a = 0 := by omega
    have hr4 := degreeIn_le_card G p.center a
    have hb4 := degreeIn_le_card G (p.vertices 2) a
    have hc4 := degreeIn_le_card G (p.vertices 3) a
    rw [(c.property.blocks_quad a ha).card] at hr4 hb4 hc4
    have hT := p.contacts_triangle a
    change contacts G p.triangle a = degreeIn G p.center a +
      (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at hT
    rw [eightWeight_eq_rows] at hweight
    refine ⟨hx0, ht0, ?_⟩
    by_cases he : degreeIn G p.center a + degreeIn G (p.vertices 3) a = 7
    · exact ⟨0, by simp; omega, by simp; omega⟩
    · exact ⟨1, by simp; omega, by simp; omega⟩

theorem exists_eight_alternative {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hcase : CaseTwo p q) : ∃ a ∈ c.blocks, a ≠ s ∧ EightAlternative p q a := by
  obtain ⟨a, ha, has, hw⟩ := exists_eight_heavy_block hc hcard hdeg hn p hp hs q hq hcase
  exact ⟨a, ha, has, every_eight_heavy_block hc hcard hdeg hn p hp hs ha has q hq hcase hw⟩

end Erdos577.JointClaims
