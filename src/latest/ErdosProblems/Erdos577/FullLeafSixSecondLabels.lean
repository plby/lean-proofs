import ErdosProblems.Erdos577.FullLeafSixOppositeExcluded

/-! A second row of size two exists and can only have adjacent cyclic neighbors. -/

namespace Erdos577.FullLeafSix

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma row_le_two (q : Quadrilateral G) (v : V)
    (h02 : ¬(G.Adj v (q 0) ∧ G.Adj v (q 2)))
    (h13 : ¬(G.Adj v (q 1) ∧ G.Adj v (q 3))) : degreeIn G v q.support ≤ 2 := by
  rw [Quadrilateral.support, degreeIn_image G v univ q q.injective, Fin.sum_univ_four]
  by_cases h0 : G.Adj v (q 0) <;> by_cases h1 : G.Adj v (q 1) <;>
    by_cases h2 : G.Adj v (q 2) <;> by_cases h3 : G.Adj v (q 3) <;> simp_all

end Erdos577.FullLeafSix

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.six_second_rows_le_two (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (ht : G.IsNClique 3 (FullLeafEquality.matchedSecond p s a y))
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (height : contacts G (s.erase y) q.support = 8)
    (hfour : contacts G (FullLeafEquality.matchedSecond p s a y) q.support = 4)
    {u : V} (hu : u ∈ s.erase y) (hrow : 3 ≤ degreeIn G u q.support) :
    ∀ v ∈ FullLeafEquality.matchedSecond p s a y, degreeIn G v q.support ≤ 2 := by
  intro v hv
  apply FullLeafSix.row_le_two
  · rintro ⟨h0, h2⟩
    exact h.six_opposite_false hcard hn ht q hj hjs hja height hfour hu hrow hv h0 h2
  · rintro ⟨h1, h3⟩
    exact h.six_opposite_false hcard hn ht (q.rotate 1)
      (by rwa [q.rotate_support]) (by rwa [q.rotate_support]) (by rwa [q.rotate_support])
      (by rwa [q.rotate_support]) (by rwa [q.rotate_support]) hu
      (by rwa [q.rotate_support]) hv h1 h3

theorem Configuration.six_adjacent_second_labels (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (ht : G.IsNClique 3 (FullLeafEquality.matchedSecond p s a y))
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (height : contacts G (s.erase y) q.support = 8)
    (hfour : contacts G (FullLeafEquality.matchedSecond p s a y) q.support = 4)
    {u : V} (hu : u ∈ s.erase y) (hrow : 3 ≤ degreeIn G u q.support) :
    ∃ v ∈ FullLeafEquality.matchedSecond p s a y, ∃ w : Quadrilateral G,
      w.support = q.support ∧ ∀ i : Fin 4, G.Adj v (w i) ↔ i = 0 ∨ i = 1 := by
  obtain ⟨v, hv, hvgt⟩ := exists_row_gt_of_contacts (G := G) (n := 1) (q := q.support)
    (by rw [ht.card_eq, hfour]; decide)
  have hvle := h.six_second_rows_le_two hcard hn ht q hj hjs hja height hfour hu hrow v hv
  obtain ⟨w, hw, hlabels | hlabels⟩ := q.exists_two_contact_labels v (by omega)
  · refine ⟨v, hv, w, hw, ?_⟩
    intro i
    rw [hlabels]
    fin_cases i <;> decide
  · exact False.elim (h.six_opposite_false hcard hn ht w (by rwa [hw]) (by rwa [hw])
      (by rwa [hw]) (by rwa [hw]) (by rwa [hw]) hu (by rwa [hw]) hv
      ((hlabels 0).mpr (by decide)) ((hlabels 2).mpr (by decide)))

end Erdos577.FullLeafCore
