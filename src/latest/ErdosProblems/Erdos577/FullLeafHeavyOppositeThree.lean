import ErdosProblems.Erdos577.FullLeafHeavyRowChoices

/-! The remaining consecutive triple is excluded by the fully discharged core obstruction. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

theorem Configuration.opposite_three_false {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a) (hfive : 5 ≤ contacts G (s.erase y) q.support)
    (hnine : 9 ≤ degreeIn G (q 0) (insert (p.vertices 3) a) +
      degreeIn G (q 2) (insert (p.vertices 3) a))
    (hX : degreeIn G p.leaf q.support = 2)
    (hopp : ∃ w ∈ insert p.leaf s, G.Adj w (q 0) ∧ G.Adj w (q 2))
    {u : V} (hu : u ∈ insert (p.vertices 3) a)
    (h0 : G.Adj u (q 0)) (h1 : G.Adj u (q 1)) (h2 : G.Adj u (q 2)) : False := by
  have hout : u ∉ q.support := fun hh ↦ disjoint_left.mp (h.core_disjoint_block hj hja)
    (h.second_five_subset hu) hh
  have hrow (i : Fin 4) (hi : i ≠ 3) : G.Adj u (q i) := by
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact False.elim (hi rfl)
  have hdiag : ¬G.Adj (q 1) (q 3) := fun hh ↦
    h.second_not_universal hcard hn hj hjs hja hfive hu
      (q.three_contacts_universal_of_diagonal u hout hrow hh)
  obtain ⟨v, hv, hvu, hv0, hv2⟩ := FullLeafHeavy.common_high_ne_of_nine
    (insert (p.vertices 3) a) h.second_five_card (q 0) (q 2) u hnine
  have h2bound := degreeIn_le_card G (q 2) (insert (p.vertices 3) a)
  rw [h.second_five_card] at h2bound
  have hlow := h.first_avoids_two_lows hcard hn q hj hjs hja (by omega)
    (mem_insert_self p.leaf s)
  rcases FullLeafHeavy.high_contact_of_two q p.leaf hX hlow with hx0 | hx2
  · exact h.remaining_opposite_core_false hcard hdeg hn q hj hjs hja hdiag hu hv hvu.symm
      h0 h1 h2 hv0 hv2 hx0 hopp
  · apply h.remaining_opposite_core_false hcard hdeg hn (q.reverse.rotate 2)
      (by simpa only [Quadrilateral.rotate_support, Quadrilateral.reverse_support] using hj)
      (by simpa only [Quadrilateral.rotate_support, Quadrilateral.reverse_support] using hjs)
      (by simpa only [Quadrilateral.rotate_support, Quadrilateral.reverse_support] using hja)
      hdiag hu hv hvu.symm h2 h1 h0 hv2 hv0 hx2
    obtain ⟨w, hw, hw0, hw2⟩ := hopp
    exact ⟨w, hw, hw2, hw0⟩

theorem Configuration.opposite_false_of_leaf_two {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    (hX : degreeIn G p.leaf q.support = 2)
    {x : V} (hx : x ∈ insert p.leaf s) (hx0 : G.Adj x (q 0)) (hx2 : G.Adj x (q 2)) : False := by
  obtain ⟨_, heleven, _, hnine, _, hfive⟩ := h.opposite_preparation hcard hn q hj hjs hja
    hheavy hrows hx hx0 hx2
  obtain ⟨u, hu, hthree⟩ := h.exists_second_three hcard hn hj hjs hja hfive heleven
  have hlow : ¬(G.Adj u (q 1) ∧ G.Adj u (q 3)) := fun hh ↦
    h.two_lows_false hcard hn q hj hjs hja hfive hnine hu hthree.ge hh.1 hh.2
  obtain ⟨h0, h2, hcase⟩ := FullLeafHeavy.three_row_without_low_pair q u hthree hlow
  rcases hcase with ⟨h1, _⟩ | ⟨_, h3⟩
  · exact h.opposite_three_false hcard hdeg hn q hj hjs hja hfive hnine hX
      ⟨x, hx, hx0, hx2⟩ hu h0 h1 h2
  · exact h.opposite_three_false hcard hdeg hn q.reverse
      (by simpa only [Quadrilateral.reverse_support] using hj)
      (by simpa only [Quadrilateral.reverse_support] using hjs)
      (by simpa only [Quadrilateral.reverse_support] using hja)
      (by simpa only [Quadrilateral.reverse_support] using hfive)
      hnine (by simpa only [Quadrilateral.reverse_support] using hX)
      ⟨x, hx, hx0, hx2⟩ hu h0 h3 h2

end Erdos577.FullLeafCore
