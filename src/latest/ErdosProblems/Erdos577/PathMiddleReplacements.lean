import ErdosProblems.Erdos577.PathRowCounts
import ErdosProblems.Erdos577.CommonReplacementAlternatives

/-! Every middle row of degree three has the replacement property in path pattern B. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma common_neighbor_of_union_bound (x y : V) (s : Finset V) (n : ℕ)
    (hbound : ((s.filter (G.Adj x)) ∪ (s.filter (G.Adj y))).card ≤ n)
    (hsum : n < degreeIn G x s + degreeIn G y s) :
    ∃ u ∈ s, G.Adj x u ∧ G.Adj y u := by
  have hid := card_union_add_card_inter (s.filter (G.Adj x)) (s.filter (G.Adj y))
  change n < (s.filter (G.Adj x)).card + (s.filter (G.Adj y)).card at hsum
  have hpos : 0 < ((s.filter (G.Adj x)) ∩ (s.filter (G.Adj y))).card := by omega
  obtain ⟨u, hu⟩ := card_pos.mp hpos
  obtain ⟨hux, huy⟩ := mem_inter.mp hu
  exact ⟨u, (mem_filter.mp hux).1, (mem_filter.mp hux).2, (mem_filter.mp huy).2⟩

namespace PathBlock

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma PatternB.column_ne_three (p : FourPath G) (q : Quadrilateral G) (h : PatternB p q)
    (i j : Fin 4) (hij : G.Adj (p.vertices i) (q j)) : j ≠ 3 := by
  have he : (j = 0 ∨ j = 1) → j ≠ 3 := by omega
  fin_cases i
  · exact he (h.1 j (Or.inl hij))
  · exact h.2 j (Or.inl hij)
  · exact h.2 j (Or.inr hij)
  · exact he (h.1 j (Or.inr hij))

lemma PatternB.union_le_three (p : FourPath G) (q : Quadrilateral G) (h : PatternB p q)
    (i l : Fin 4) :
    ((q.support.filter (G.Adj (p.vertices i))) ∪
      (q.support.filter (G.Adj (p.vertices l)))).card ≤ 3 := by
  have hs : ((q.support.filter (G.Adj (p.vertices i))) ∪
      (q.support.filter (G.Adj (p.vertices l)))) ⊆ {q 0, q 1, q 2} := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    all_goals
      obtain ⟨hvq, hvrow⟩ := mem_filter.mp hv
      obtain ⟨j, rfl⟩ := (q.mem_support v).mp hvq
    · have hj := h.column_ne_three p q i j hvrow
      fin_cases j <;> simp_all
    · have hj := h.column_ne_three p q l j hvrow
      fin_cases j <;> simp_all
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  have hcard : ({q 0, q 1, q 2} : Finset V).card = 3 := by simp [hinj.eq_iff]
  exact (card_le_card hs).trans (le_of_eq hcard)

lemma PatternB.end_union_le_two (p : FourPath G) (q : Quadrilateral G) (h : PatternB p q) :
    ((q.support.filter (G.Adj (p.vertices 0))) ∪
      (q.support.filter (G.Adj (p.vertices 3)))).card ≤ 2 := by
  have hs : ((q.support.filter (G.Adj (p.vertices 0))) ∪
      (q.support.filter (G.Adj (p.vertices 3)))) ⊆ {q 0, q 1} := by
    intro v hv
    rcases mem_union.mp hv with hv | hv
    all_goals
      obtain ⟨hvq, hvrow⟩ := mem_filter.mp hv
      obtain ⟨j, rfl⟩ := (q.mem_support v).mp hvq
    · rcases h.1 j (Or.inl hvrow) with rfl | rfl <;> simp
    · rcases h.1 j (Or.inr hvrow) with rfl | rfl <;> simp
  have hinj : Function.Injective (q : Fin 4 → V) := q.injective
  have hcard : ({q 0, q 1} : Finset V).card = 2 := by simp [hinj.eq_iff]
  exact (card_le_card hs).trans (le_of_eq hcard)

lemma PatternB.middle_row_subset (p : FourPath G) (q : Quadrilateral G)
    (h : PatternB p q) (hrow : degreeIn G (p.vertices 2) q.support = 3)
    (u : V) (hu : u ∈ q.support) (hru : G.Adj (p.vertices 1) u) :
    G.Adj (p.vertices 2) u := by
  have hsub : q.support.filter (G.Adj (p.vertices 2)) ⊆ q.support.erase (q 3) := by
    intro v hv
    obtain ⟨hvq, hcv⟩ := mem_filter.mp hv
    refine mem_erase.mpr ⟨?_, hvq⟩
    intro he
    rw [he] at hcv
    exact h.column_ne_three p q 2 3 hcv rfl
  have hcard : (q.support.erase (q 3)).card = 3 := by
    rw [card_erase_of_mem ((q.mem_support _).mpr ⟨3, rfl⟩), q.card_support]
  have he := eq_of_subset_of_card_le hsub (by
    change (q.support.erase (q 3)).card ≤ degreeIn G (p.vertices 2) q.support
    rw [hcard, hrow])
  have hne : u ≠ q 3 := by
    intro he
    rw [he] at hru
    exact h.column_ne_three p q 1 3 hru rfl
  exact (mem_filter.mp (he.symm ▸ mem_erase.mpr ⟨hne, hu⟩)).2

lemma PatternB.common_for_middle (p : FourPath G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (hq : G.IsNClique 4 q.support)
    (h : PatternB p q) (hheavy : 9 ≤ contacts G p.support q.support)
    (i : Fin 4) (hi : i = 1 ∨ i = 2) (hrow : degreeIn G (p.vertices i) q.support = 3)
    (j l : Fin 4) (hji : j ≠ i) (hli : l ≠ i) (hjl : j ≠ l) :
    CommonReplacement G (p.vertices j) (p.vertices l) (p.vertices i) q.support := by
  obtain ⟨h0, h1, h2, h3⟩ := h.row_bounds p q
  have htotal := p.contacts_support q.support
  have hendpoints : ∃ u ∈ q.support, G.Adj (p.vertices 0) u ∧ G.Adj (p.vertices 3) u := by
    apply common_neighbor_of_union_bound _ _ q.support 2 (h.end_union_le_two p q)
    omega
  have hcommon : ∃ u ∈ q.support, G.Adj (p.vertices j) u ∧ G.Adj (p.vertices l) u := by
    by_cases he : (j = 0 ∧ l = 3) ∨ (j = 3 ∧ l = 0)
    · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hendpoints
      · obtain ⟨u, hu, h0u, h3u⟩ := hendpoints
        exact ⟨u, hu, h3u, h0u⟩
    · apply common_neighbor_of_union_bound _ _ q.support 3 (h.union_le_three p q j l)
      rcases hi with rfl | rfl
      · fin_cases j <;> fin_cases l
        · exact False.elim (hjl rfl)
        · exact False.elim (hli rfl)
        · change 3 < degreeIn G (p.vertices 0) q.support + degreeIn G (p.vertices 2) q.support
          omega
        · exact False.elim (he (Or.inl ⟨rfl, rfl⟩))
        · exact False.elim (hji rfl)
        · exact False.elim (hji rfl)
        · exact False.elim (hji rfl)
        · exact False.elim (hji rfl)
        · change 3 < degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 0) q.support
          omega
        · exact False.elim (hli rfl)
        · exact False.elim (hjl rfl)
        · change 3 < degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 3) q.support
          omega
        · exact False.elim (he (Or.inr ⟨rfl, rfl⟩))
        · exact False.elim (hli rfl)
        · change 3 < degreeIn G (p.vertices 3) q.support + degreeIn G (p.vertices 2) q.support
          omega
        · exact False.elim (hjl rfl)
      · fin_cases j <;> fin_cases l
        · exact False.elim (hjl rfl)
        · change 3 < degreeIn G (p.vertices 0) q.support + degreeIn G (p.vertices 1) q.support
          omega
        · exact False.elim (hli rfl)
        · exact False.elim (he (Or.inl ⟨rfl, rfl⟩))
        · change 3 < degreeIn G (p.vertices 1) q.support + degreeIn G (p.vertices 0) q.support
          omega
        · exact False.elim (hjl rfl)
        · exact False.elim (hli rfl)
        · change 3 < degreeIn G (p.vertices 1) q.support + degreeIn G (p.vertices 3) q.support
          omega
        · exact False.elim (hji rfl)
        · exact False.elim (hji rfl)
        · exact False.elim (hji rfl)
        · exact False.elim (hji rfl)
        · exact False.elim (he (Or.inr ⟨rfl, rfl⟩))
        · change 3 < degreeIn G (p.vertices 3) q.support + degreeIn G (p.vertices 1) q.support
          omega
        · exact False.elim (hli rfl)
        · exact False.elim (hjl rfl)
  obtain ⟨u, hu, hju, hlu⟩ := hcommon
  have hout : p.vertices i ∉ q.support := by
    intro hv
    exact disjoint_left.mp hd ((p.mem_support _).mpr ⟨i, rfl⟩) hv
  exact ⟨u, hu, hju, hlu, clique_replace_of_degree_three hq hout (by omega) hu⟩

end PathBlock

end Erdos577
