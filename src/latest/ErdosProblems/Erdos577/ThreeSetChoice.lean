import Mathlib.Data.Finset.Card

/-! Enumerate a three-set while retaining one or two specified elements. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V]

lemma exists_pair_in_three_set {t : Finset V} (ht : t.card = 3) (z : V) (hz : z ∈ t) :
    ∃ x y : V, x ≠ y ∧ z ≠ x ∧ z ≠ y ∧ t = {z, x, y} := by
  have hc : (t.erase z).card = 2 := by rw [card_erase_of_mem hz, ht]
  obtain ⟨x, y, hxy, he⟩ := card_eq_two.mp hc
  have hx : x ∈ t.erase z := by rw [he]; exact mem_insert_self _ _
  have hy : y ∈ t.erase z := by rw [he]; exact mem_insert_of_mem (mem_singleton_self _)
  exact ⟨x, y, hxy, (mem_erase.mp hx).1.symm, (mem_erase.mp hy).1.symm,
    by rw [← insert_erase hz, he]⟩

lemma exists_third_in_three_set {t : Finset V} (ht : t.card = 3)
    (x y : V) (hx : x ∈ t) (hy : y ∈ t) (hxy : x ≠ y) :
    ∃ z : V, z ≠ x ∧ z ≠ y ∧ t = {x, y, z} := by
  have hy' : y ∈ t.erase x := mem_erase.mpr ⟨hxy.symm, hy⟩
  have hc : ((t.erase x).erase y).card = 1 := by
    rw [card_erase_of_mem hy', card_erase_of_mem hx, ht]
  obtain ⟨z, he⟩ := card_eq_one.mp hc
  have hz : z ∈ (t.erase x).erase y := by rw [he]; exact mem_singleton_self _
  refine ⟨z, (mem_erase.mp (mem_erase.mp hz).2).1, (mem_erase.mp hz).1, ?_⟩
  calc
    t = insert x (t.erase x) := (insert_erase hx).symm
    _ = insert x (insert y ((t.erase x).erase y)) :=
      congrArg (insert x) (insert_erase hy').symm
    _ = {x, y, z} := by rw [he]

end Erdos577
