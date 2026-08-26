import ErdosProblems.Erdos421.LongGaps

/-! # Prime-free starts in an actual dyadic interval -/

namespace Erdos421

def primeFreeDyadicStarts (X H : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter (fun m ↦ ∀ p ∈ Finset.Icc m (m + H), ¬ p.Prime)

theorem mem_primeFreeDyadicStarts {X H m : ℕ} : m ∈ primeFreeDyadicStarts X H ↔
    X ≤ m ∧ m < 2 * X ∧ ∀ p ∈ Finset.Icc m (m + H), ¬ p.Prime := by
  simp only [primeFreeDyadicStarts, Finset.mem_filter, Finset.mem_Ico]
  tauto

theorem primeFreeStarts_card_le (B H : ℕ) : (primeFreeStarts B H).card ≤ B :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range B)

theorem primeFreeStarts_double_card (X H : ℕ) :
    (primeFreeStarts (2 * X) H).card =
      (primeFreeStarts X H).card + (primeFreeDyadicStarts X H).card := by
  have hunion : primeFreeStarts (2 * X) H = primeFreeStarts X H ∪ primeFreeDyadicStarts X H := by
    ext m
    simp only [primeFreeStarts, primeFreeDyadicStarts, Finset.mem_filter, Finset.mem_range,
      Finset.mem_union, Finset.mem_Ico]
    constructor
    · rintro ⟨hm, hfree⟩
      by_cases hmx : m < X
      · exact Or.inl ⟨hmx, hfree⟩
      · exact Or.inr ⟨⟨by omega, hm⟩, hfree⟩
    · rintro (⟨hm, hfree⟩ | ⟨⟨_, hm⟩, hfree⟩)
      · exact ⟨by omega, hfree⟩
      · exact ⟨hm, hfree⟩
  have hdisjoint : Disjoint (primeFreeStarts X H) (primeFreeDyadicStarts X H) := by
    apply Finset.disjoint_left.mpr
    intro m hm hn
    have hlo := (mem_primeFreeDyadicStarts.mp hn).1
    have hhi := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
    omega
  rw [hunion, Finset.card_union_of_disjoint hdisjoint]

end Erdos421
