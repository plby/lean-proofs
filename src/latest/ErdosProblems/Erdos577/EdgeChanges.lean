import ErdosProblems.Erdos577.CopyCounts

/-! Exact induced-edge changes for disjoint unions and vertex replacement. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma edgeCount_union {s t : Finset V} (h : Disjoint s t) :
    edgeCount G (s ∪ t) = edgeCount G s + edgeCount G t + contacts G s t := by
  have hc := contacts_self_eq_twice_edgeCount G (s ∪ t)
  rw [contacts_union_left G h, contacts_union_right G s h,
    contacts_union_right G t h, contacts_self_eq_twice_edgeCount,
    contacts_self_eq_twice_edgeCount, contacts_comm G t s] at hc
  omega

omit [DecidableEq V] in
@[simp] lemma edgeCount_singleton (v : V) : edgeCount G {v} = 0 := by
  have h := edgeCount_le_choose_two G {v}
  apply Nat.eq_zero_of_le_zero
  simpa only [card_singleton, Nat.choose_eq_zero_of_lt (by decide : 1 < 2)] using h

lemma edgeCount_insert (v : V) {s : Finset V} (hv : v ∉ s) :
    edgeCount G (insert v s) = edgeCount G s + degreeIn G v s := by
  rw [← singleton_union, edgeCount_union G (disjoint_singleton_left.mpr hv),
    edgeCount_singleton, contacts_singleton_left, Nat.zero_add]

lemma degreeIn_erase_add (v w : V) {s : Finset V} (hw : w ∈ s) :
    degreeIn G v (s.erase w) + (if G.Adj v w then 1 else 0) = degreeIn G v s := by
  have h := degreeIn_insert G v w (s := s.erase w) (by simp)
  rw [insert_erase hw] at h
  omega

lemma degreeIn_erase_self (v : V) {s : Finset V} (hv : v ∈ s) :
    degreeIn G v (s.erase v) = degreeIn G v s := by
  have h := degreeIn_erase_add G v v hv
  simpa only [SimpleGraph.irrefl, if_false, Nat.add_zero] using h

lemma edgeCount_erase_add (v : V) {s : Finset V} (hv : v ∈ s) :
    edgeCount G (s.erase v) + degreeIn G v s = edgeCount G s := by
  have h := edgeCount_insert G v (s := s.erase v) (by simp)
  rw [insert_erase hv, degreeIn_erase_self G v hv] at h
  exact h.symm

/-- The additive form avoids truncated subtraction in all later score comparisons. -/
lemma edgeCount_replace (v x : V) {s : Finset V} (hv : v ∈ s) (hx : x ∉ s) :
    edgeCount G (insert x (s.erase v)) + degreeIn G v s =
      edgeCount G s + degreeIn G x (s.erase v) := by
  have hxe : x ∉ s.erase v := fun h ↦ hx (mem_erase.mp h).2
  rw [edgeCount_insert G x hxe]
  have he := edgeCount_erase_add G v hv
  omega

end Erdos577
