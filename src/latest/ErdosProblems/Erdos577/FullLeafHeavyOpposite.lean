import ErdosProblems.Erdos577.FullLeafHeavyOppositeThree

/-! All opposite pairs are excluded, restoring both marked leaves by the actual interchange. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.no_opposite_first_pair (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 2)
    {x : V} (hx : x ∈ insert p.leaf s) : ¬(G.Adj x (q 0) ∧ G.Adj x (q 2)) := by
  rintro ⟨hx0, hx2⟩
  by_cases hX : degreeIn G p.leaf q.support = 2
  · exact h.opposite_false_of_leaf_two hcard hdeg hn q hj hjs hja hheavy hrows hX hx hx0 hx2
  · obtain ⟨_, _, _, _, hnine, _⟩ := h.opposite_preparation hcard hn q hj hjs hja
      hheavy hrows hx hx0 hx2
    have htriple : contacts G (s.erase y) q.support ≤ 6 := by
      calc
        contacts G (s.erase y) q.support ≤ ∑ _ ∈ s.erase y, (2 : ℕ) :=
          sum_le_sum fun z hz ↦ hrows z (mem_insert_of_mem (mem_erase.mp hz).2)
        _ = 6 := by simp only [sum_const, smul_eq_mul, h.first_triple_clique.card_eq]
    have hsplit := h.first_contacts q.support
    have hXbound := hrows p.leaf (mem_insert_self _ _)
    have hYbound := hrows y (mem_insert_of_mem h.exposed)
    have hY : degreeIn G y q.support = 2 := by omega
    obtain ⟨e, p', he, _, hleaf, _, _, hthird, _, _, _, hblocks, _⟩ :=
      h.swapped_chain hcard hn
    obtain ⟨hj', hjs', hja'⟩ := (h.swapped_outside_blocks hblocks q.support).mp ⟨hj, hjs, hja⟩
    have hfirst : insert p'.leaf (insert p.leaf (s.erase y)) = insert p.leaf s := by
      rw [hleaf, h.first_five_swap]
    apply he.opposite_false_of_leaf_two hcard hdeg hn q hj' hjs' hja'
      (by simpa only [hfirst, hthird] using hheavy)
      (by simpa only [hfirst] using hrows)
      (by simpa only [hleaf] using hY) (by simpa only [hfirst] using hx) hx0 hx2

end Erdos577.FullLeafCore
