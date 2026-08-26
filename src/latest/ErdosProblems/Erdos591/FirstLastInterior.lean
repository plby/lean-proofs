import ErdosProblems.Erdos591.FirstLastLabels

/-! # Interior stopping indices of the common-first/common-last labels -/

namespace Erdos591.Positive.Game.FirstLastLabels

variable {H : Set ℕ} {B p q : ℕ}

def lowerPenultimate (L : FirstLastLabels H B p q) : ℕ := (L.lower.erase L.last).sup id

def upperPenultimate (L : FirstLastLabels H B p q) : ℕ := (L.upper.erase L.last).sup id

def upperNext (L : FirstLastLabels H B p q) : ℕ :=
  (L.upper.erase L.first).min'
    ⟨L.last, Finset.mem_erase.mpr ⟨L.first_lt_last.ne.symm, L.last_upper⟩⟩

theorem lowerPenultimate_mem_erase (L : FirstLastLabels H B p q) :
    L.lowerPenultimate ∈ L.lower.erase L.last := by
  simpa [lowerPenultimate, and_comm] using Finset.sup_mem_of_nonempty (f := id)
    ⟨L.first, Finset.mem_erase.mpr ⟨L.first_lt_last.ne, L.first_lower⟩⟩

theorem upperPenultimate_mem_erase (L : FirstLastLabels H B p q) :
    L.upperPenultimate ∈ L.upper.erase L.last := by
  simpa [upperPenultimate, and_comm] using Finset.sup_mem_of_nonempty (f := id)
    ⟨L.first, Finset.mem_erase.mpr ⟨L.first_lt_last.ne, L.first_upper⟩⟩

theorem lowerPenultimate_mem (L : FirstLastLabels H B p q) : L.lowerPenultimate ∈ L.lower :=
  Finset.mem_of_mem_erase L.lowerPenultimate_mem_erase

theorem upperPenultimate_mem (L : FirstLastLabels H B p q) : L.upperPenultimate ∈ L.upper :=
  Finset.mem_of_mem_erase L.upperPenultimate_mem_erase

theorem lowerPenultimate_lt_last (L : FirstLastLabels H B p q) : L.lowerPenultimate < L.last :=
  lt_of_le_of_ne (L.lower_bounds _ L.lowerPenultimate_mem).2
    (Finset.ne_of_mem_erase L.lowerPenultimate_mem_erase)

theorem upperPenultimate_lt_last (L : FirstLastLabels H B p q) : L.upperPenultimate < L.last :=
  lt_of_le_of_ne (L.upper_bounds _ L.upperPenultimate_mem).2
    (Finset.ne_of_mem_erase L.upperPenultimate_mem_erase)

theorem lower_bounds_penultimate (L : FirstLastLabels H B p q) (x : ℕ) (hx : x ∈ L.lower) :
    x = L.last ∨ x ≤ L.lowerPenultimate := by
  by_cases heq : x = L.last
  · exact Or.inl heq
  · exact Or.inr (Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨heq, hx⟩))

theorem upper_bounds_penultimate (L : FirstLastLabels H B p q) (x : ℕ) (hx : x ∈ L.upper) :
    x = L.last ∨ x ≤ L.upperPenultimate := by
  by_cases heq : x = L.last
  · exact Or.inl heq
  · exact Or.inr (Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨heq, hx⟩))

theorem upperNext_mem_erase (L : FirstLastLabels H B p q) :
    L.upperNext ∈ L.upper.erase L.first := Finset.min'_mem _ _

theorem upperNext_mem (L : FirstLastLabels H B p q) : L.upperNext ∈ L.upper :=
  Finset.mem_of_mem_erase L.upperNext_mem_erase

theorem first_lt_upperNext (L : FirstLastLabels H B p q) : L.first < L.upperNext :=
  lt_of_le_of_ne (L.upper_bounds _ L.upperNext_mem).1
    (Finset.ne_of_mem_erase L.upperNext_mem_erase).symm

theorem upperNext_le (L : FirstLastLabels H B p q) (x : ℕ) (hx : x ∈ L.upper)
    (hfirst : L.first < x) : L.upperNext ≤ x :=
  Finset.min'_le _ _ (Finset.mem_erase.mpr ⟨hfirst.ne.symm, hx⟩)

theorem lowerPenultimate_lt_upperNext (L : FirstLastLabels H B p q) :
    L.lowerPenultimate < L.upperNext :=
  L.separated _ L.lowerPenultimate_mem _ L.upperNext_mem
    L.lowerPenultimate_lt_last.ne L.first_lt_upperNext.ne.symm

private theorem exists_middle (A : Finset ℕ) {first last : ℕ} (hf : first ∈ A) (hl : last ∈ A)
    (hne : first ≠ last) (hcard : 3 ≤ A.card) :
    ∃ x, x ∈ A ∧ x ≠ first ∧ x ≠ last := by
  have hlast : last ∈ A.erase first := Finset.mem_erase.mpr ⟨hne.symm, hl⟩
  have hpos : 0 < ((A.erase first).erase last).card := by
    rw [Finset.card_erase_of_mem hlast, Finset.card_erase_of_mem hf]
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hxlast := Finset.mem_erase.mp hx
  have hxfirst := Finset.mem_erase.mp hxlast.2
  exact ⟨x, hxfirst.2, hxfirst.1, hxlast.1⟩

theorem first_lt_lowerPenultimate (L : FirstLastLabels H B p q) (hp : 3 ≤ p) :
    L.first < L.lowerPenultimate := by
  obtain ⟨x, hx, hxf, hxl⟩ := exists_middle L.lower L.first_lower L.last_lower
    L.first_lt_last.ne (by simpa only [L.lower_card] using hp)
  exact (lt_of_le_of_ne (L.lower_bounds x hx).1 hxf.symm).trans_le
    (Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨hxl, hx⟩))

theorem upperNext_le_upperPenultimate (L : FirstLastLabels H B p q) (hq : 3 ≤ q) :
    L.upperNext ≤ L.upperPenultimate := by
  obtain ⟨x, hx, hxf, hxl⟩ := exists_middle L.upper L.first_upper L.last_upper
    L.first_lt_last.ne (by simpa only [L.upper_card] using hq)
  exact (L.upperNext_le x hx (lt_of_le_of_ne (L.upper_bounds x hx).1 hxf.symm)).trans
    (Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨hxl, hx⟩))

#print axioms first_lt_lowerPenultimate
#print axioms upperNext_le_upperPenultimate
#print axioms lowerPenultimate_lt_upperNext

theorem lower_eq_pair (L : FirstLastLabels H B p q) (hp : p = 2) :
    L.lower = {L.first, L.last} := by
  have hsub : {L.first, L.last} ⊆ L.lower := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact L.first_lower
    · exact Finset.mem_singleton.mp hx ▸ L.last_lower
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [L.lower_card, hp, L.first_lt_last.ne])).symm

theorem upper_eq_pair (L : FirstLastLabels H B p q) (hq : q = 2) :
    L.upper = {L.first, L.last} := by
  have hsub : {L.first, L.last} ⊆ L.upper := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact L.first_upper
    · exact Finset.mem_singleton.mp hx ▸ L.last_upper
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [L.upper_card, hq, L.first_lt_last.ne])).symm

#print axioms lower_eq_pair
#print axioms upper_eq_pair

end Erdos591.Positive.Game.FirstLastLabels
