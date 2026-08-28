import ErdosProblems.Erdos577.FullLeafHeavyMarkedContact

/-! Both original marked leaves have zero rows in the degree-one branch. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.second_contacts_ge_sixteen {j : Finset V}
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x j ≤ 1) :
    16 ≤ contacts G (insert (p.vertices 3) a) j := by
  have hs : contacts G (insert p.leaf s) j ≤ 5 := by
    calc
      contacts G (insert p.leaf s) j ≤ ∑ _ ∈ insert p.leaf s, (1 : ℕ) := sum_le_sum hrows
      _ = 5 := by simp only [sum_const, smul_eq_mul, mul_one, h.first_five_clique.card_eq]
  rw [h.combined_contacts] at hheavy
  omega

theorem Configuration.centers_not_both_four :
    ¬(degreeIn G p.center (insert (p.vertices 3) a) = 4 ∧
      degreeIn G (p.vertices 2) (insert (p.vertices 3) a) = 4) := by
  rintro ⟨hr4, hb4⟩
  have hout : p.vertices 3 ∉ a := fun hh ↦ disjoint_left.mp (h.paw_disjoint h.core)
    ((mem_tupleSupport p.vertices _).mpr ⟨3, rfl⟩) hh
  have hr := degreeIn_insert G p.center (p.vertices 3) hout
  have hb := degreeIn_insert G (p.vertices 2) (p.vertices 3) hout
  rw [if_pos (show G.Adj p.center (p.vertices 3) from p.edge13)] at hr
  rw [if_pos p.edge23] at hb
  have hthird := degreeIn_le_card G (p.vertices 3) a
  rw [h.core_clique.card_eq] at hthird
  have hsum := p.contacts_triangle a
  change contacts G p.triangle a = degreeIn G p.center a +
    (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at hsum
  have hdense := h.dense
  omega

theorem Configuration.marked_rows_zero {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (q : Quadrilateral G) (hj : q.support ∈ c.blocks) (hjs : q.support ≠ s)
    (hja : q.support ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) q.support)
    (hrows : ∀ x ∈ insert p.leaf s, degreeIn G x q.support ≤ 1) :
    degreeIn G p.leaf q.support = 0 ∧ degreeIn G y q.support = 0 := by
  have hsixteen := h.second_contacts_ge_sixteen hheavy hrows
  have hd := (h.core_disjoint_block hj hja).mono_left h.second_five_subset
  obtain ⟨hr, hb⟩ := h.center_degrees
  have hfirst (hpos : 1 ≤ degreeIn G p.leaf q.support) :
      degreeIn G p.center (insert (p.vertices 3) a) = 4 ∧
        contacts G (insert (p.vertices 3) a) q.support = 16 :=
    FullLeafHeavy.marked_positive_center_eq_four q (insert (p.vertices 3) a) h.second_five_card
      hd hsixteen p.leaf p.center hpos hr (fun _ hu _ hv hne hvc ↦
        h.center_common_forbidden hcard hn hu hv hne hvc hj hjs hja)
  have hsecond (hpos : 1 ≤ degreeIn G y q.support) :
      degreeIn G (p.vertices 2) (insert (p.vertices 3) a) = 4 ∧
        contacts G (insert (p.vertices 3) a) q.support = 16 :=
    FullLeafHeavy.marked_positive_center_eq_four q (insert (p.vertices 3) a) h.second_five_card
      hd hsixteen y (p.vertices 2) hpos hb (fun _ hu _ hv hne hvc ↦
        h.second_common_forbidden hcard hn hu hv hne hvc hj hjs hja)
  have htriple : contacts G (s.erase y) q.support ≤ 3 := by
    calc
      contacts G (s.erase y) q.support ≤ ∑ _ ∈ s.erase y, (1 : ℕ) :=
        sum_le_sum fun w hw ↦ hrows w (mem_insert_of_mem (mem_erase.mp hw).2)
      _ = 3 := by simp only [sum_const, smul_eq_mul, mul_one, h.first_triple_clique.card_eq]
  have hsplit := h.first_contacts q.support
  have hX := hrows p.leaf (mem_insert_self _ _)
  have hY := hrows y (mem_insert_of_mem h.exposed)
  have hheavy' := hheavy
  rw [h.combined_contacts] at hheavy'
  have hnone : ¬(1 ≤ degreeIn G p.leaf q.support ∨ 1 ≤ degreeIn G y q.support) := by
    intro hpos
    have he : contacts G (insert (p.vertices 3) a) q.support = 16 := by
      rcases hpos with hpos | hpos
      · exact (hfirst hpos).2
      · exact (hsecond hpos).2
    have hXpos : 1 ≤ degreeIn G p.leaf q.support := by omega
    have hYpos : 1 ≤ degreeIn G y q.support := by omega
    exact h.centers_not_both_four ⟨(hfirst hXpos).1, (hsecond hYpos).1⟩
  exact ⟨by omega, by omega⟩

end Erdos577.FullLeafCore
