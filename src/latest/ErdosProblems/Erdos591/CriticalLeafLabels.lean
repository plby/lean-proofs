import ErdosProblems.Erdos591.CriticalRootLabels

/-!
# Prescribed lower critical leaf equal to the first upper leaf

In the nonlast alternative, the lower maximum is the second upper
selection. A fresh prefix places the common first-upper selection at
any prescribed positive nonfinal lower rank. Both full label sizes
are fixed before the common body marker is read.
-/

namespace Erdos591.Positive.Game

structure CriticalLeafLabels (H : Set ℕ) (B n c s : ℕ) where
  lower : Finset ℕ
  upperView : LastFirstLabels H B 1 c
  lower_card : lower.card = n
  pivot_lower : upperView.pivot ∈ lower
  pivot_rank : (lower.filter (fun x => x ≤ upperView.pivot)).card = s
  pivot_lt_last : upperView.pivot < lower.sup id
  last_upper : lower.sup id ∈ upperView.upper
  upper_next : ∀ x ∈ upperView.upper, upperView.pivot < x → lower.sup id ≤ x
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < upperView.marker

namespace CriticalLeafLabels

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B n c s : ℕ)
    (hs : 0 < s) (hsn : s < n) (hc : 2 ≤ c) : Nonempty (CriticalLeafLabels H B n c s) := by
  classical
  obtain ⟨f, hf, hfH, hfB, _⟩ := FastSequence.exists_above_finite_bounds hH ∅ (fun _ => B)
  let A := (Finset.range (s - 1)).image f
  let P := f (s - 1)
  have hAcard : A.card = s - 1 := by
    simp [A, Finset.card_image_of_injective _ hf.injective]
  have hA (x : ℕ) (hx : x ∈ A) : x ∈ H ∧ B < x ∧ x < P := by
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hfH k, hfB k, hf (Finset.mem_range.mp hk)⟩
  obtain ⟨R⟩ := CriticalRootLabels.exists_of_infinite hH P c (n - s + 1) 1
    (by omega) (by omega) (by omega)
  have hPshared : P < R.shared := (R.lower_fresh _ R.shared_lower).2.1
  have hPmarker : P < R.marker := R.marker_fresh.2
  have hupperMin (x : ℕ) (hx : x ∈ R.lower) : R.shared ≤ x := by
    by_cases hle : x ≤ R.shared
    · have heq := Finset.card_le_one.mp R.shared_rank.le x (Finset.mem_filter.mpr ⟨hx, hle⟩)
        R.shared (Finset.mem_filter.mpr ⟨R.shared_lower, le_rfl⟩)
      exact heq.ge
    · exact (lt_of_not_ge hle).le
  let U : LastFirstLabels H B 1 c := {
    lower := {R.shared}
    upper := R.lower
    pivot := R.shared
    marker := R.marker
    lower_card := by simp
    upper_card := R.lower_card
    pivot_lower := by simp
    pivot_upper := R.shared_lower
    lower_le := fun _ hx => (Finset.mem_singleton.mp hx).le
    upper_ge := hupperMin
    lower_fresh := by
      intro x hx
      rw [Finset.mem_singleton.mp hx]
      have h := R.lower_fresh _ R.shared_lower
      exact ⟨h.1, (hfB _).trans h.2.1, h.2.2⟩
    upper_fresh := by
      intro x hx
      have h := R.lower_fresh x hx
      exact ⟨h.1, (hfB _).trans h.2.1, h.2.2⟩
    marker_fresh := ⟨R.marker_fresh.1, (hfB _).trans hPmarker⟩ }
  let D := A ∪ R.upper
  have hdisjoint : Disjoint A R.upper := by
    apply Finset.disjoint_left.mpr
    intro x hx hR
    exact not_lt_of_ge (hA x hx).2.2.le (R.upper_fresh x hR).2.1
  have hsup : D.sup id = R.next := by
    apply le_antisymm
    · apply Finset.sup_le
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact ((hA x hx).2.2.trans (hPshared.trans R.shared_lt_next)).le
      · exact (R.upper_bounds x hx).2
    · exact Finset.le_sup (f := id) (Finset.mem_union_right _ R.next_upper)
  have hrank : D.filter (fun x => x ≤ R.shared) = insert R.shared A := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hle⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_insert_of_mem hx
      · exact Finset.mem_insert.mpr (Or.inl (le_antisymm hle (R.upper_bounds x hx).1))
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨Finset.mem_union_right _ R.shared_upper, le_rfl⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_union_left _ hx, ((hA x hx).2.2.trans hPshared).le⟩
  refine ⟨⟨D, U, ?_, Finset.mem_union_right _ R.shared_upper, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Finset.card_union_of_disjoint hdisjoint, hAcard, R.upper_card]
    omega
  · change (D.filter (fun x => x ≤ R.shared)).card = s
    rw [hrank, Finset.card_insert_of_notMem, hAcard]
    · omega
    · exact fun h => not_lt_of_ge (hA _ h).2.2.le hPshared
  · change R.shared < D.sup id
    rw [hsup]
    exact R.shared_lt_next
  · change D.sup id ∈ R.lower
    rw [hsup]
    exact R.next_lower
  · change ∀ x ∈ R.lower, R.shared < x → D.sup id ≤ x
    rw [hsup]
    exact R.next_is_next
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact ⟨(hA x hx).1, (hA x hx).2.1, (hA x hx).2.2.trans hPmarker⟩
    · have h := R.upper_fresh x hx
      exact ⟨h.1, (hfB _).trans h.2.1, h.2.2⟩

#print axioms exists_of_infinite

end CriticalLeafLabels

end Erdos591.Positive.Game
