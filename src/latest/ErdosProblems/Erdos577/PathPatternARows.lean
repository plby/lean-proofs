import ErdosProblems.Erdos577.PathRowCounts

/-! Full and almost-full rows, and the exact outer-row bounds in path pattern A. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma Quadrilateral.degree_le_three_of_nonadjacent (q : Quadrilateral G) (z : V)
    (i : Fin 4) (h : ¬G.Adj z (q i)) : degreeIn G z q.support ≤ 3 := by
  have hm : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
  have he := degreeIn_erase_add G z (q i) hm
  rw [if_neg h] at he
  have hb := degreeIn_le_card G z (q.support.erase (q i))
  rw [card_erase_of_mem hm, q.card_support] at hb
  omega

lemma Quadrilateral.adj_iff_ne_three (q : Quadrilateral G) (z : V)
    (hrow : degreeIn G z q.support = 3) (hn : ¬G.Adj z (q 3)) (j : Fin 4) :
    G.Adj z (q j) ↔ j ≠ 3 := by
  have hsub : q.support.filter (G.Adj z) ⊆ q.support.erase (q 3) := by
    intro v hv
    obtain ⟨hvq, hzv⟩ := mem_filter.mp hv
    exact mem_erase.mpr ⟨fun he ↦ hn (he ▸ hzv), hvq⟩
  have hcard : (q.support.erase (q 3)).card = 3 := by
    rw [card_erase_of_mem ((q.mem_support _).mpr ⟨3, rfl⟩), q.card_support]
  have he := eq_of_subset_of_card_le hsub (by
    change (q.support.erase (q 3)).card ≤ degreeIn G z q.support
    rw [hcard, hrow])
  constructor
  · intro hj heq
    exact hn (heq ▸ hj)
  · intro hj
    have hm : q j ∈ q.support.erase (q 3) :=
      mem_erase.mpr ⟨fun heq ↦ hj (q.injective heq), (q.mem_support _).mpr ⟨j, rfl⟩⟩
    exact (mem_filter.mp (he.symm ▸ hm)).2

lemma Quadrilateral.adj_of_degree_four (q : Quadrilateral G) (z : V)
    (hrow : degreeIn G z q.support = 4) (u : V) (hu : u ∈ q.support) : G.Adj z u := by
  have he : q.support.filter (G.Adj z) = q.support :=
    eq_of_subset_of_card_le (filter_subset _ _) (by
      change q.support.card ≤ degreeIn G z q.support
      rw [q.card_support, hrow])
  exact (mem_filter.mp (he.symm ▸ hu)).2

namespace PathBlock

lemma PatternA.outer_nonadjacent (p : FourPath G) (q : Quadrilateral G) (h : PatternA p q)
    (i : Fin 4) (hi : i = 0 ∨ i = 2) : ¬G.Adj (p.vertices i) (q 3) := by
  intro he
  apply h.1 3 _ rfl
  rcases hi with rfl | rfl
  · exact Or.inl he
  · exact Or.inr he

lemma PatternA.row_bounds (p : FourPath G) (q : Quadrilateral G) (h : PatternA p q) :
    degreeIn G (p.vertices 0) q.support ≤ 3 ∧
      3 ≤ degreeIn G (p.vertices 1) q.support ∧ degreeIn G (p.vertices 1) q.support ≤ 4 ∧
      degreeIn G (p.vertices 2) q.support ≤ 3 ∧ degreeIn G (p.vertices 3) q.support = 0 :=
  ⟨q.degree_le_three_of_nonadjacent _ 3 (h.outer_nonadjacent p q 0 (Or.inl rfl)),
    h.2.1, h.2.2.1,
    q.degree_le_three_of_nonadjacent _ 3 (h.outer_nonadjacent p q 2 (Or.inr rfl)), h.2.2.2⟩

lemma PatternA.outer_two_le (p : FourPath G) (q : Quadrilateral G) (h : PatternA p q)
    (hh : 9 ≤ contacts G p.support q.support) :
    2 ≤ degreeIn G (p.vertices 0) q.support ∧ 2 ≤ degreeIn G (p.vertices 2) q.support := by
  obtain ⟨h0, _, h1, h2, h3⟩ := h.row_bounds p q
  have he := p.contacts_support q.support
  omega

end PathBlock

end Erdos577
