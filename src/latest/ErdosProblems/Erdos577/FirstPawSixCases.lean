import ErdosProblems.Erdos577.FirstPawSixCounts
import ErdosProblems.Erdos577.FirstPawSixEssential

/-! Exactly one critical contact is missing, giving the five source cases (22)–(26). -/

namespace Erdos577.FirstPawSix

open Finset

def caseRows : Fin 5 → Fin 4 → ℕ :=
  ![![3, 14, 7, 1], ![3, 15, 7, 0], ![3, 15, 5, 1], ![3, 15, 3, 1], ![2, 15, 7, 1]]

lemma allowed_index_iff (i j : Fin 4) :
    ((![3, 15, 7, 1] : Fin 4 → ℕ) i).testBit j.val = true ↔
      ∃ t : Fin 10, row t = i ∧ column t = j := by
  have hall : ∀ i j : Fin 4,
      ((![3, 15, 7, 1] : Fin 4 → ℕ) i).testBit j.val = true ↔
        ∃ t : Fin 10, row t = i ∧ column t = j := by decide +kernel
  exact hall i j

lemma case_index_iff (tag : Fin 5) (i j : Fin 4) :
    (caseRows tag i).testBit j.val = true ↔
      ∃ t : Fin 10, t ≠ critical tag ∧ row t = i ∧ column t = j := by
  have hall : ∀ i j : Fin 4, (caseRows tag i).testBit j.val = true ↔
      ∃ t : Fin 10, t ≠ critical tag ∧ row t = i ∧ column t = j := by
    fin_cases tag <;> decide +kernel
  exact hall i j

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exact_case_of_not_essential (p : Paw G) (q : Quadrilateral G)
    (h : PawBlock.Pattern6 p q) (hheavy : 9 ≤ contacts G p.support q.support)
    (hne : ¬Essential p q) : ∃ tag : Fin 5, PawBlock.ExactRows p q (caseRows tag) := by
  obtain ⟨tag, hmiss⟩ := not_forall.mp hne
  let P := fun i : Fin 10 ↦ G.Adj (p.vertices (row i)) (q (column i))
  have hcount : 9 ≤ (univ.filter P).card := by rw [allowed_contact_count p q h]; exact hheavy
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin 10))) P
  have hcard : (univ : Finset (Fin 10)).card = 10 := by decide
  have hsmall : (univ.filter fun i ↦ ¬P i).card ≤ 1 := by omega
  have hothers (i : Fin 10) (hi : i ≠ critical tag) : P i := by
    by_contra hh
    exact hi (card_le_one.mp hsmall i (mem_filter.mpr ⟨mem_univ i, hh⟩)
      (critical tag) (mem_filter.mpr ⟨mem_univ _, hmiss⟩))
  refine ⟨tag, ?_⟩
  intro i j
  constructor
  · intro hadj
    obtain ⟨t, rfl, rfl⟩ := (allowed_index_iff i j).mp (allowed_row p q h i j hadj)
    apply (case_index_iff tag _ _).mpr
    refine ⟨t, ?_, rfl, rfl⟩
    intro ht
    subst t
    exact hmiss hadj
  · intro hbit
    obtain ⟨t, ht, rfl, rfl⟩ := (case_index_iff tag i j).mp hbit
    exact hothers t ht

variable [Fintype V]

theorem exact_cases {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : PawBlock.Pattern6 p q)
    (hheavy : 9 ≤ contacts G p.support q.support) :
    ∃ tag : Fin 5, PawBlock.ExactRows p q (caseRows tag) :=
  exact_case_of_not_essential p q h hheavy
    (not_essential hc hcard hdeg hn p hp hb q hq hd h hheavy)

end Erdos577.FirstPawSix
