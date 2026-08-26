import ErdosProblems.Erdos118.Reused591.PreliminaryPivotLabels
import ErdosProblems.Erdos118.Reused591.FiniteRank

namespace Erdos118.Reused591

/-! # The shared beta is the next selection after each preliminary rank -/

namespace Erdos591.Positive.Game

theorem finite_rank_eq_strict_rank_add_one {α : Type*} [LinearOrder α]
    (C : Finset α) {y : α} (hy : y ∈ C) :
    (C.filter (fun x => x ≤ y)).card = (C.filter (fun x => x < y)).card + 1 := by
  classical
  have heq : C.filter (fun x => x ≤ y) = insert y (C.filter (fun x => x < y)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hle⟩
      rcases lt_or_eq_of_le hle with hlt | rfl
      · exact Or.inr ⟨hx, hlt⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hx, hlt⟩)
      · exact ⟨hy, le_rfl⟩
      · exact ⟨hx, hlt.le⟩
  rw [heq, Finset.card_insert_of_notMem]
  simp

namespace PreliminaryPivotLabels

variable {H : Set ℕ} {B p q r t : ℕ}

theorem beta_next_lower_of_rank (L : PreliminaryPivotLabels H B p q r t) {x : ℕ}
    (hr : (L.lower.filter (fun z => z ≤ x)).card = r) :
    x < L.beta ∧ ∀ z ∈ L.lower, x < z → L.beta ≤ z := by
  apply finite_rank_successor L.lower L.beta_lower
  rw [finite_rank_eq_strict_rank_add_one L.lower L.beta_lower, L.lower_before, hr]

theorem beta_next_upper_of_rank (L : PreliminaryPivotLabels H B p q r t) {x : ℕ}
    (ht : (L.upper.filter (fun z => z ≤ x)).card = t) :
    x < L.beta ∧ ∀ z ∈ L.upper, x < z → L.beta ≤ z := by
  apply finite_rank_successor L.upper L.beta_upper
  rw [finite_rank_eq_strict_rank_add_one L.upper L.beta_upper, L.upper_before, ht]

#print axioms beta_next_lower_of_rank
#print axioms beta_next_upper_of_rank

theorem upper_min_of_zero (L : PreliminaryPivotLabels H B p q r 0) :
    L.upper.min' ⟨_, L.beta_upper⟩ = L.beta := by
  apply le_antisymm (L.upper.min'_le _ L.beta_upper)
  have hnone : L.upper.filter (fun x => x < L.beta) = ∅ :=
    Finset.card_eq_zero.mp L.upper_before
  by_contra hn
  have hmem : L.upper.min' ⟨_, L.beta_upper⟩ ∈ L.upper.filter (fun x => x < L.beta) :=
    Finset.mem_filter.mpr
    ⟨L.upper.min'_mem ⟨_, L.beta_upper⟩, lt_of_not_ge hn⟩
  rw [hnone] at hmem
  exact Finset.notMem_empty _ hmem

#print axioms upper_min_of_zero

end PreliminaryPivotLabels

end Erdos591.Positive.Game

end Erdos118.Reused591
