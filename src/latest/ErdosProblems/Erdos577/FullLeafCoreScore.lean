import ErdosProblems.Erdos577.FullLeafCoreCommon

/-! The two marked vertices avoid the second five-set, so their interchange preserves contacts. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}
variable (h : Configuration c p s a y)

include h

lemma Configuration.marked_row_zero {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) {x w : V} (hx : x ∈ insert p.leaf s)
    (hw : w ∈ p.triangle ∪ a) (hxw : G.Adj x w) (hwout : w ∉ insert (p.vertices 3) a) :
    degreeIn G x (insert (p.vertices 3) a) = 0 := by
  have hrow := (FullRow.unique_row_of_bound (p.triangle ∪ a) x w hw hxw
    (h.first_core_degree hcard hn hx)).2
  rw [degreeIn, card_eq_zero]
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hv, hxv⟩ := mem_filter.mp hv
  have he := (hrow v (h.second_five_subset hv)).mp hxv
  exact hwout (he ▸ hv)

theorem Configuration.marked_degrees_zero {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) :
    degreeIn G p.leaf (insert (p.vertices 3) a) = 0 ∧
      degreeIn G y (insert (p.vertices 3) a) = 0 := by
  constructor
  · exact h.marked_row_zero hcard hn (mem_insert_self _ _)
      (mem_union_left _ p.center_mem_triangle) p.pendant
      (fun hh ↦ (h.second_avoids hh).2.1 rfl)
  · exact h.marked_row_zero hcard hn (mem_insert_of_mem h.exposed)
      (mem_union_left _ (by simp [Paw.triangle])) h.attached.symm
      (fun hh ↦ (h.second_avoids hh).2.2 rfl)

theorem Configuration.objective_swap {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hn : ¬HasPacking G k) :
    contacts G (insert (p.vertices 3) a) (insert p.leaf (s.erase y)) =
      contacts G (insert (p.vertices 3) a) s := by
  obtain ⟨hx, hy⟩ := h.marked_degrees_zero hcard hn
  have hsum := sum_erase_add (s := s) (fun v ↦ degreeIn G v (insert (p.vertices 3) a)) h.exposed
  have hout : p.leaf ∉ s.erase y := fun hh ↦ h.leaf_out (mem_erase.mp hh).2
  rw [contacts_comm G (insert (p.vertices 3) a) (insert p.leaf (s.erase y)),
    contacts_comm G (insert (p.vertices 3) a) s, contacts, sum_insert hout, hx, zero_add]
  simpa only [hy, add_zero, contacts] using hsum

lemma Configuration.first_five_swap :
    insert y (insert p.leaf (s.erase y)) = insert p.leaf s := by
  rw [insert_comm y p.leaf, insert_erase h.exposed]

lemma Configuration.first_triple_swap :
    (insert p.leaf (s.erase y)).erase p.leaf = s.erase y :=
  erase_insert (fun hh ↦ h.leaf_out (mem_erase.mp hh).2)

end Erdos577.FullLeafCore
