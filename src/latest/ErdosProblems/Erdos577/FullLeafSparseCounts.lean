import ErdosProblems.Erdos577.FullLeafSparseAvoid

/-! The matching and sparse rows occupy disjoint vertices of the second five-set. -/

namespace Erdos577.FullLeafSparse

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma contacts_eq_positive_rows {z j : Finset V}
    (hrows : ∀ u ∈ z, degreeIn G u j ≤ 1) :
    contacts G z j = (z.filter (fun u ↦ 0 < degreeIn G u j)).card := by
  classical
  rw [contacts, card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro u hu
  have hb := hrows u hu
  split_ifs <;> omega

omit [DecidableEq V] in
lemma full_column_of_seventeen {z j : Finset V} (hz : z.card = 5) (hj : j.card = 4)
    (hcontacts : 17 ≤ contacts G z j) :
    ∃ d ∈ j, degreeIn G d z = 5 := by
  classical
  by_contra! hnone
  have hsum : contacts G j z ≤ 16 := by
    calc
      contacts G j z ≤ ∑ _ ∈ j, (4 : ℕ) := by
        apply sum_le_sum
        intro d hd
        have hb := degreeIn_le_card G d z
        have hne := hnone d hd
        rw [hz] at hb
        omega
      _ = 16 := by simp only [sum_const, smul_eq_mul, hj]
  rw [contacts_comm G j z] at hsum
  omega

end Erdos577.FullLeafSparse

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.objective_eq_matching {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    contacts G (insert (p.vertices 3) a) s = contacts G (s.erase y) (insert (p.vertices 3) a) := by
  have hzero := (h.marked_degrees_zero hcard hn).2
  have he := sum_erase_add (s := s) (fun v ↦ degreeIn G v (insert (p.vertices 3) a)) h.exposed
  rw [hzero, add_zero] at he
  rw [contacts_comm G (insert (p.vertices 3) a) s]
  exact he.symm

theorem Configuration.matching_add_type41_contacts_le_five {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {j : Finset V} (hj : j ∈ c.blocks) (hjs : j ≠ s) (hja : j ≠ a)
    (hheavy : 21 ≤ contacts G ((insert p.leaf s) ∪ insert (p.vertices 3) a) j)
    (htype : FullLeafHeavy.Type41 G p a j) :
    contacts G (s.erase y) (insert (p.vertices 3) a) +
      contacts G (insert (p.vertices 3) a) j ≤ 5 := by
  let m := (insert (p.vertices 3) a).filter (fun u ↦ 0 < degreeIn G u (s.erase y))
  let b := (insert (p.vertices 3) a).filter (fun u ↦ 0 < degreeIn G u j)
  have hm : contacts G (insert (p.vertices 3) a) (s.erase y) = m.card :=
    FullLeafSparse.contacts_eq_positive_rows (h.matching_degrees hcard hn).2
  have hb : contacts G (insert (p.vertices 3) a) j = b.card :=
    FullLeafSparse.contacts_eq_positive_rows htype.1
  have hd : Disjoint m b := by
    apply disjoint_left.mpr
    intro u hum hub
    obtain ⟨hu, hpos⟩ := mem_filter.mp hum
    obtain ⟨w, hw⟩ := card_pos.mp hpos
    obtain ⟨hw, huw⟩ := mem_filter.mp hw
    have hz := h.type41_matching_endpoint_zero hcard hn hj hjs hja hheavy htype hw hu huw.symm
    have hbpos := (mem_filter.mp hub).2
    omega
  have hbound : (m ∪ b).card ≤ 5 :=
    (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans_eq
      h.second_five_card
  rw [card_union_of_disjoint hd, ← hm, ← hb, contacts_comm G (insert (p.vertices 3) a) (s.erase y)]
    at hbound
  exact hbound

end Erdos577.FullLeafCore
