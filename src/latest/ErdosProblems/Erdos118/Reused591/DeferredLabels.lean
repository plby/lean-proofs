import ErdosProblems.Erdos118.Reused591.LastLastLabels

namespace Erdos118.Reused591

/-!
# A finite family of deferred upper labels

From a saved last--first pair, erase the greatest upper label and insert
any nonlast lower selected index. The upper cardinality is unchanged.
The old pivot is the second upper index unless the request is singleton.
All candidates use only values already reserved below the same marker.
-/

namespace Erdos591.Positive.Game.LastFirstLabels

variable {H : Set ℕ} {B a c : ℕ}

def deferredUpper (L : LastFirstLabels H B a c) (j : ℕ) : Finset ℕ :=
  insert j (L.upper.erase (L.upper.sup id))

theorem upper_sup_mem (L : LastFirstLabels H B a c) : L.upper.sup id ∈ L.upper := by
  simpa using Finset.sup_mem_of_nonempty (f := id) ⟨L.pivot, L.pivot_upper⟩

theorem deferredUpper_card (L : LastFirstLabels H B a c) {j : ℕ} (hj : j < L.pivot) :
    (L.deferredUpper j).card = c := by
  have hnot : j ∉ L.upper.erase (L.upper.sup id) := by
    intro h
    exact (not_lt_of_ge (L.upper_ge j (Finset.mem_of_mem_erase h))) hj
  have hc : 0 < c := L.upper_card ▸ Finset.card_pos.mpr ⟨L.pivot, L.pivot_upper⟩
  rw [deferredUpper, Finset.card_insert_of_notMem hnot,
    Finset.card_erase_of_mem L.upper_sup_mem, L.upper_card]
  omega

theorem deferredUpper_min (L : LastFirstLabels H B a c) {j : ℕ} (hj : j < L.pivot) :
    j ∈ L.deferredUpper j ∧ ∀ x ∈ L.deferredUpper j, j ≤ x := by
  refine ⟨Finset.mem_insert_self _ _, ?_⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact le_rfl
  · exact hj.le.trans (L.upper_ge x (Finset.mem_of_mem_erase hx))

theorem deferredUpper_fresh (L : LastFirstLabels H B a c) {j : ℕ} (hj : j ∈ L.lower) :
    ∀ x ∈ L.deferredUpper j, x ∈ H ∧ B < x ∧ x < L.marker := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact L.lower_fresh _ hj
  · exact L.upper_fresh x (Finset.mem_of_mem_erase hx)

theorem deferredUpper_singleton (L : LastFirstLabels H B a c) (hc : c = 1) (j : ℕ) :
    L.deferredUpper j = {j} := by
  have he : L.upper.erase (L.upper.sup id) = ∅ := by
    apply Finset.card_eq_zero.mp
    rw [Finset.card_erase_of_mem L.upper_sup_mem, L.upper_card, hc]
  simp [deferredUpper, he]

theorem deferredUpper_second (L : LastFirstLabels H B a c) (hc : 2 ≤ c)
    {j : ℕ} (hj : j < L.pivot) :
    L.pivot ∈ L.deferredUpper j ∧
      ∀ x ∈ L.deferredUpper j, j < x → L.pivot ≤ x := by
  have hp : L.pivot ∈ L.upper.erase (L.upper.sup id) :=
    Finset.mem_erase.mpr ⟨(L.pivot_lt_upper_sup hc).ne, L.pivot_upper⟩
  refine ⟨Finset.mem_insert_of_mem hp, ?_⟩
  intro x hx hlt
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact (Nat.lt_irrefl _ hlt).elim
  · exact L.upper_ge x (Finset.mem_of_mem_erase hx)

theorem deferredUpper_intersection (L : LastFirstLabels H B a c) (hc : 2 ≤ c)
    {j : ℕ} (hj : j ∈ L.lower) (hlt : j < L.pivot) :
    L.lower ∩ L.deferredUpper j = {j, L.pivot} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hu⟩
    rcases Finset.mem_insert.mp hu with he | hu
    · exact Or.inl he
    · exact Or.inr (le_antisymm (L.lower_le x hl)
        (L.upper_ge x (Finset.mem_of_mem_erase hu)))
  · rintro (rfl | rfl)
    · exact ⟨hj, (L.deferredUpper_min hlt).1⟩
    · exact ⟨L.pivot_lower, (L.deferredUpper_second hc hlt).1⟩

def deferredFirst (L : LastFirstLabels H B a c) (j : ℕ)
    (hj : j ∈ L.lower) (hlt : j < L.pivot) : LastFirstLabels H B 1 c where
  lower := {j}
  upper := L.deferredUpper j
  pivot := j
  marker := L.marker
  lower_card := by simp
  upper_card := L.deferredUpper_card hlt
  pivot_lower := by simp
  pivot_upper := (L.deferredUpper_min hlt).1
  lower_le := by
    intro x hx
    exact (Finset.mem_singleton.mp hx).le
  upper_ge := (L.deferredUpper_min hlt).2
  lower_fresh := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact L.lower_fresh j hj
  upper_fresh := L.deferredUpper_fresh hj
  marker_fresh := L.marker_fresh

#print axioms deferredUpper_card
#print axioms deferredUpper_singleton
#print axioms deferredUpper_second
#print axioms deferredUpper_intersection

end Erdos591.Positive.Game.LastFirstLabels

end Erdos118.Reused591
