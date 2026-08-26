import ErdosProblems.Erdos591.DoubleOverlapLabels

/-!
# First-leaf overlap with an optional lower-last/upper-second shared selection

A singleton lower label needs only the common first index. Otherwise
both sizes are at least two, and the lower maximum is the upper second
selection. The two views share the marker and first index exactly.
-/

namespace Erdos591.Positive.Game

theorem first_second_label_choice {H : Set ℕ} (hH : H.Infinite) (B p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hcompat : 2 ≤ p → 2 ≤ q) :
    ∃ L : LastFirstLabels H B 1 p, ∃ U : LastFirstLabels H B 1 q,
      U.pivot = L.pivot ∧ U.marker = L.marker ∧
      (p = 1 ∨ (L.pivot < L.upper.sup id ∧ L.upper.sup id ∈ U.upper ∧
        ∀ j ∈ U.upper, L.pivot < j → L.upper.sup id ≤ j)) := by
  by_cases hpLarge : 2 ≤ p
  · obtain ⟨D⟩ := DoubleOverlapLabels.exists_sizes_of_infinite hH B p q hpLarge (hcompat hpLarge)
    have hlast : D.lower.sup id = D.pivot :=
      le_antisymm (Finset.sup_le (fun x hx => (D.lower_bounds x hx).2))
        (Finset.le_sup (f := id) D.pivot_lower)
    refine ⟨D.first_to_lower, D.first_to_upper, rfl, rfl, Or.inr ?_⟩
    change D.first < D.lower.sup id ∧ D.lower.sup id ∈ D.upper ∧
      ∀ j ∈ D.upper, D.first < j → D.lower.sup id ≤ j
    rw [hlast]
    refine ⟨D.first_lt_pivot, D.pivot_upper, ?_⟩
    intro j hj hlt
    exact (D.upper_bounds j hj).resolve_left (ne_of_gt hlt)
  · have hpOne : p = 1 := by omega
    subst p
    obtain ⟨U⟩ := LastFirstLabels.exists_of_infinite hH B 1 q (by omega) hq
    let L : LastFirstLabels H B 1 1 :=
      { lower := {U.pivot}
        upper := {U.pivot}
        pivot := U.pivot
        marker := U.marker
        lower_card := by simp
        upper_card := by simp
        pivot_lower := by simp
        pivot_upper := by simp
        lower_le := fun _ hx => (Finset.mem_singleton.mp hx).le
        upper_ge := fun _ hx => (Finset.mem_singleton.mp hx).ge
        lower_fresh := by
          intro x hx
          rw [Finset.mem_singleton.mp hx]
          exact U.upper_fresh _ U.pivot_upper
        upper_fresh := by
          intro x hx
          rw [Finset.mem_singleton.mp hx]
          exact U.upper_fresh _ U.pivot_upper
        marker_fresh := U.marker_fresh }
    exact ⟨L, U, rfl, rfl, Or.inl rfl⟩

#print axioms first_second_label_choice

end Erdos591.Positive.Game
