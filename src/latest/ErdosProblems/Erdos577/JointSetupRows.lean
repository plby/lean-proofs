import ErdosProblems.Erdos577.FullRowSwap

/-! The two precise starting cases and the triangle column restriction in TeX9.47. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def CaseOne (p : Paw G) (q : Quadrilateral G) : Prop :=
  degreeIn G p.leaf q.support = 4 ∧ G.Adj p.center (q 1) ∧
    G.Adj (p.vertices 2) (q 2) ∧ G.Adj (p.vertices 2) (q 3)

def CaseTwo (p : Paw G) (q : Quadrilateral G) : Prop :=
  7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support ∧
    (degreeIn G p.leaf q.support = 4 → ∀ i : Fin 4, i ≠ 0 → G.Adj (p.vertices 2) (q i)) ∧
    (degreeIn G p.leaf q.support = 3 → ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ i ≠ 3)

lemma leaf_lower (p : Paw G) (q : Quadrilateral G) (h : CaseOne p q ∨ CaseTwo p q) :
    3 ≤ degreeIn G p.leaf q.support := by
  have hb := degreeIn_le_card G (p.vertices 2) q.support
  rw [q.card_support] at hb
  rcases h with h | h
  · rw [h.1]
    decide
  · have hh := h.1
    omega

lemma first_rows (p : Paw G) (q : Quadrilateral G) (h : CaseOne p q ∨ CaseTwo p q) :
    (∀ i : Fin 4, i ≠ 3 → G.Adj p.leaf (q i)) ∧ G.Adj (p.vertices 2) (q 3) := by
  have hmem (i : Fin 4) : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have hleaf := degreeIn_le_card G p.leaf q.support
  have hb := degreeIn_le_card G (p.vertices 2) q.support
  rw [q.card_support] at hleaf hb
  rcases h with h | h
  · exact ⟨fun i _ ↦ (degreeIn_eq_card_iff p.leaf q.support).mp
      (h.1.trans q.card_support.symm) (q i) (hmem i), h.2.2.2⟩
  · by_cases hfour : degreeIn G p.leaf q.support = 4
    · exact ⟨fun i _ ↦ (degreeIn_eq_card_iff p.leaf q.support).mp
        (hfour.trans q.card_support.symm) (q i) (hmem i), h.2.1 hfour 3 (by decide)⟩
    · have hseven := h.1
      have hthree : degreeIn G p.leaf q.support = 3 := by omega
      have hbfull : degreeIn G (p.vertices 2) q.support = 4 := by omega
      exact ⟨fun i hi ↦ (h.2.2 hthree i).mpr hi,
        (degreeIn_eq_card_iff (p.vertices 2) q.support).mp
          (hbfull.trans q.card_support.symm) (q 3) (hmem 3)⟩

variable [Fintype V]

theorem triangle_column_le_one {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (hthree : 3 ≤ degreeIn G p.leaf s)
    (u : V) (hu : u ∈ s) : degreeIn G u p.triangle ≤ 1 := by
  let d := c.presentPaw p hp
  have hrep := (hc.presentPaw_feasible p hp).terminal_universal_replace hs hthree hu
  exact (d.replaceBlock s hs (d.swapTerminal hs hu hrep)).terminal_degree_le_one hcard hn

theorem triangle_contacts_le_four {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (hthree : 3 ≤ degreeIn G p.leaf s) :
    contacts G p.triangle s ≤ 4 := by
  rw [contacts_comm]
  calc
    _ ≤ ∑ _ ∈ s, 1 := sum_le_sum fun u hu ↦ triangle_column_le_one hc hcard hn p hp hs hthree u hu
    _ = 4 := by simp [(c.property.blocks_quad s hs).card]

theorem triangle_rows_disjoint {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (hthree : 3 ≤ degreeIn G p.leaf s)
    (a b : V) (ha : a ∈ p.triangle) (hb : b ∈ p.triangle) (hne : a ≠ b) :
    Disjoint (s.filter (G.Adj a)) (s.filter (G.Adj b)) := by
  apply disjoint_left.mpr
  intro u hu hv
  have hcol := triangle_column_le_one hc hcard hn p hp hs hthree u (mem_filter.mp hu).1
  have hpair : ({a, b} : Finset V) ⊆ p.triangle.filter (G.Adj u) :=
    insert_subset (mem_filter.mpr ⟨ha, (mem_filter.mp hu).2.symm⟩)
      (singleton_subset_iff.mpr (mem_filter.mpr ⟨hb, (mem_filter.mp hv).2.symm⟩))
  have hcount := card_le_card hpair
  rw [card_pair_eq_two_iff.mpr hne] at hcount
  change 2 ≤ degreeIn G u p.triangle at hcount
  omega

theorem case_two_universal {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (h : CaseTwo p q) (u : V) (hu : u ∈ q.support) :
    QuadOn G (insert (p.vertices 2) (q.support.erase u)) := by
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  exact FullRow.noncentral_universal hc p hp hs q hq hd (first_rows p q (Or.inr h)).1 h.1 u hu

end Erdos577.JointClaims
