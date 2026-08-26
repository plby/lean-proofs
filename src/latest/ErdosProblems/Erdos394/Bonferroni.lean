import Mathlib

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite even Bonferroni truncation
-/

open Nat Finset

namespace Erdos394

/-- A truncated alternating binomial sum is an upper bound for the empty-set
indicator when the truncation order is even. -/
theorem indicator_le_even_alternatingChoose (r R : ℕ) (hR : Even R) :
    (if r = 0 then 1 else 0 : ℤ) ≤
      ∑ k ∈ Finset.range (R + 1), ((-1 : ℤ) ^ k) * r.choose k := by
  by_cases hr : r = 0
  · subst r
    simp only [if_pos]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      simp
    · simp
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    have hform := Int.alternating_sum_range_choose_eq_choose
      (n := r - 1) (m := R)
    rw [Nat.sub_add_cancel hrpos] at hform
    rw [if_neg hr, hform, hR.neg_one_pow]
    exact Int.natCast_nonneg _

/-- Sum a cardinality-dependent function over subsets of size at most `R`. -/
theorem sum_powerset_card_le (s : Finset α) (R : ℕ) (f : ℕ → A)
    [AddCommMonoid A] :
    (∑ t ∈ s.powerset.filter (fun t ↦ t.card ≤ R), f t.card) =
      ∑ k ∈ Finset.range (R + 1), s.card.choose k • f k := by
  classical
  trans ∑ k ∈ Finset.range (R + 1),
      ∑ t ∈ (s.powerset.filter (fun t ↦ t.card ≤ R)).filter
        (fun t ↦ t.card = k), f t.card
  · refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
    intro t ht
    simp only [Finset.mem_filter] at ht
    simp [ht.2]
  · apply Finset.sum_congr rfl
    intro k hk
    have hkR : k ≤ R := by simpa using hk
    have hfiber :
        (s.powerset.filter (fun t ↦ t.card ≤ R)).filter
            (fun t ↦ t.card = k) = s.powersetCard k := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_powerset,
        Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨hts, _⟩, hcard⟩
        exact ⟨hts, hcard⟩
      · rintro ⟨hts, hcard⟩
        exact ⟨⟨hts, hcard ▸ hkR⟩, hcard⟩
    rw [hfiber, ← Finset.card_powersetCard, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro t ht
    rw [(Finset.mem_powersetCard.mp ht).2]

/-- Even truncation of inclusion-exclusion over a finite set is an upper bound
for the indicator that the set is empty. -/
theorem bonferroni_powerset_upper [DecidableEq α]
    (s : Finset α) (R : ℕ) (hR : Even R) :
    (if s = ∅ then 1 else 0 : ℤ) ≤
      ∑ t ∈ s.powerset.filter (fun t ↦ t.card ≤ R), (-1 : ℤ) ^ t.card := by
  classical
  rw [sum_powerset_card_le s R (fun k ↦ (-1 : ℤ) ^ k)]
  simp only [nsmul_eq_mul]
  have h := indicator_le_even_alternatingChoose s.card R hR
  simpa only [Finset.card_eq_zero, mul_comm] using h

end Erdos394
