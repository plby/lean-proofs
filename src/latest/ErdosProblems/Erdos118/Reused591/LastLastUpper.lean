import ErdosProblems.Erdos118.Reused591.LastLastLabels

namespace Erdos118.Reused591

/-!
# Penultimate selected index of the upper common-last root label

The upper label has a nonlast entry. Erasing its common maximum leaves
a nonempty finite set, whose maximum supplies the inserted lower play's
penultimate body index and the required next-body stopping bounds.
-/

namespace Erdos591.Positive.Game.LastLastLabels

variable {H : Set ℕ} {B n c : ℕ}

def upperPenultimate (L : LastLastLabels H B n c) : ℕ := (L.upper.erase L.pivot).sup id

theorem upper_erase_nonempty (L : LastLastLabels H B n c) :
    (L.upper.erase L.pivot).Nonempty := by
  obtain ⟨x, hx, hlt⟩ := L.upper_before_pivot
  exact ⟨x, Finset.mem_erase.mpr ⟨hlt.ne, hx⟩⟩

theorem upperPenultimate_mem_erase (L : LastLastLabels H B n c) :
    L.upperPenultimate ∈ L.upper.erase L.pivot := by
  simpa [upperPenultimate, and_comm] using
    Finset.sup_mem_of_nonempty (f := id) L.upper_erase_nonempty

theorem upperPenultimate_mem (L : LastLastLabels H B n c) : L.upperPenultimate ∈ L.upper :=
  Finset.mem_of_mem_erase L.upperPenultimate_mem_erase

theorem upperPenultimate_lt_pivot (L : LastLastLabels H B n c) : L.upperPenultimate < L.pivot :=
  lt_of_le_of_ne (L.upper_bounds _ L.upperPenultimate_mem).2
    (Finset.ne_of_mem_erase L.upperPenultimate_mem_erase)

theorem firstUpper_le_upperPenultimate (L : LastLastLabels H B n c) :
    L.firstUpper ≤ L.upperPenultimate := L.firstUpper_le _ L.upperPenultimate_mem

theorem upper_bounds_penultimate (L : LastLastLabels H B n c) (x : ℕ) (hx : x ∈ L.upper) :
    x = L.pivot ∨ x ≤ L.upperPenultimate := by
  by_cases heq : x = L.pivot
  · exact Or.inl heq
  · exact Or.inr (Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨heq, hx⟩))

#print axioms upperPenultimate_mem
#print axioms upperPenultimate_lt_pivot
#print axioms upper_bounds_penultimate

end Erdos591.Positive.Game.LastLastLabels

end Erdos118.Reused591
