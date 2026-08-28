import ErdosProblems.Erdos577.FullLeafHeavyMarkedRows

/-! The final degree-one branch gives zero marked rows and the first-triple matching type. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.low_first_matching (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 1) :
    degreeIn G p.leaf q.support = 0 ∧ degreeIn G y q.support = 0 ∧
      (∀ x ∈ s.erase y, degreeIn G x q.support ≤ 1) ∧
      ∀ v ∈ q.support, degreeIn G v (s.erase y) ≤ 1 := by
  obtain ⟨hX, hY⟩ := h.marked_rows_zero hcard hn q hj hjs hja hheavy hrows
  have htripleRows (x : V) (hx : x ∈ s.erase y) : degreeIn G x q.support ≤ 1 :=
    hrows x (mem_insert_of_mem (mem_erase.mp hx).2)
  have htriple : contacts G (s.erase y) q.support ≤ 3 := by
    calc
      contacts G (s.erase y) q.support ≤ ∑ _ ∈ s.erase y, (1 : ℕ) := sum_le_sum htripleRows
      _ = 3 := by simp only [sum_const, smul_eq_mul, mul_one, h.first_triple_clique.card_eq]
  have hsplit := h.first_contacts q.support
  rw [h.combined_contacts] at hheavy
  have heighteen : 18 ≤ contacts G (insert (p.vertices 3) a) q.support := by omega
  have hfull : ∃ u ∈ insert (p.vertices 3) a, degreeIn G u q.support = 4 := by
    by_contra! hnone
    have hsum : contacts G (insert (p.vertices 3) a) q.support ≤ 15 := by
      calc
        contacts G (insert (p.vertices 3) a) q.support ≤
            ∑ _ ∈ insert (p.vertices 3) a, (3 : ℕ) := by
          apply sum_le_sum
          intro u hu
          have hb := degreeIn_le_card G u q.support
          rw [q.card_support] at hb
          have hne := hnone u hu
          omega
        _ = 15 := by simp only [sum_const, smul_eq_mul, h.second_five_card]
    omega
  obtain ⟨u, hu, hufull⟩ := hfull
  have hout : u ∉ q.support := fun hh ↦
    disjoint_left.mp (h.core_disjoint_block hj hja) (h.second_five_subset hu) hh
  refine ⟨hX, hY, htripleRows, ?_⟩
  intro v hv
  exact h.triple_degree_of_second_replacement hcard hn hu hj hjs hja hv
    ((show QuadOn G q.support from ⟨q, rfl⟩).replace_of_degree_four hout hufull hv)

end Erdos577.FullLeafCore
