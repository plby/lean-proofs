import ErdosProblems.Erdos118.Reused591.OverlapLabels

namespace Erdos118.Reused591

/-!
# Overlap at the first and last/second selected indices

For sizes at least two, choose two labels with a common first
index, with the lower label's last index equal to the upper label's
second index, and with no other common indices. This is the finite
label configuration used at either the body or root level inside.
-/

namespace Erdos591.Positive.Game

structure DoubleOverlapLabels (H : Set ℕ) (B n : ℕ) (c : ℕ := n) where
  lower : Finset ℕ
  upper : Finset ℕ
  first : ℕ
  pivot : ℕ
  marker : ℕ
  lower_card : lower.card = n
  upper_card : upper.card = c
  first_lower : first ∈ lower
  first_upper : first ∈ upper
  pivot_lower : pivot ∈ lower
  pivot_upper : pivot ∈ upper
  first_lt_pivot : first < pivot
  lower_bounds : ∀ x ∈ lower, first ≤ x ∧ x ≤ pivot
  upper_bounds : ∀ x ∈ upper, x = first ∨ pivot ≤ x
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < marker
  upper_fresh : ∀ x ∈ upper, x ∈ H ∧ B < x ∧ x < marker
  marker_fresh : marker ∈ H ∧ B < marker

namespace DoubleOverlapLabels

theorem exists_sizes_of_infinite {H : Set ℕ} (hH : H.Infinite) (B n c : ℕ)
    (hn : 2 ≤ n) (hc : 2 ≤ c) : Nonempty (DoubleOverlapLabels H B n c) := by
  classical
  obtain ⟨f, _hf, hfH, hfB, _⟩ := FastSequence.exists_above_finite_bounds hH ∅ (fun _ => B)
  let first := f 0
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH first (n - 1) (c - 1) (by omega) (by omega)
  have hfirstLower : first ∉ L.lower := fun h => Nat.lt_irrefl _ (L.lower_fresh first h).2.1
  have hfirstUpper : first ∉ L.upper := fun h => Nat.lt_irrefl _ (L.upper_fresh first h).2.1
  have hfp : first < L.pivot := (L.lower_fresh L.pivot L.pivot_lower).2.1
  have hfm : first < L.marker := L.marker_fresh.2
  refine ⟨⟨insert first L.lower, insert first L.upper, first, L.pivot, L.marker,
    ?_, ?_, by simp, by simp, by simp [L.pivot_lower], by simp [L.pivot_upper], hfp,
    ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [Finset.card_insert_of_notMem hfirstLower, L.lower_card]
    omega
  · rw [Finset.card_insert_of_notMem hfirstUpper, L.upper_card]
    omega
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨le_rfl, hfp.le⟩
    · exact ⟨(L.lower_fresh x hx).2.1.le, L.lower_le x hx⟩
  · intro x hx
    exact (Finset.mem_insert.mp hx).elim Or.inl (fun hx => Or.inr (L.upper_ge x hx))
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hfH 0, hfB 0, hfm⟩
    · exact ⟨(L.lower_fresh x hx).1, (hfB 0).trans (L.lower_fresh x hx).2.1,
        (L.lower_fresh x hx).2.2⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hfH 0, hfB 0, hfm⟩
    · exact ⟨(L.upper_fresh x hx).1, (hfB 0).trans (L.upper_fresh x hx).2.1,
        (L.upper_fresh x hx).2.2⟩
  · exact ⟨L.marker_fresh.1, (hfB 0).trans hfm⟩

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B n : ℕ) (hn : 2 ≤ n) :
    Nonempty (DoubleOverlapLabels H B n) := exists_sizes_of_infinite hH B n n hn hn

theorem intersection {H : Set ℕ} {B n c : ℕ} (L : DoubleOverlapLabels H B n c) :
    L.lower ∩ L.upper = {L.first, L.pivot} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hu⟩
    rcases L.upper_bounds x hu with he | he
    · exact Or.inl he
    · exact Or.inr (le_antisymm (L.lower_bounds x hl).2 he)
  · rintro (rfl | rfl)
    · exact ⟨L.first_lower, L.first_upper⟩
    · exact ⟨L.pivot_lower, L.pivot_upper⟩

/-- View the common first index as a singleton lower label and the
full lower label as its upper label, for the first-leaf response API. -/
def first_to_lower {H : Set ℕ} {B n c : ℕ} (L : DoubleOverlapLabels H B n c) :
    LastFirstLabels H B 1 n where
  lower := {L.first}
  upper := L.lower
  pivot := L.first
  marker := L.marker
  lower_card := by simp
  upper_card := L.lower_card
  pivot_lower := by simp
  pivot_upper := L.first_lower
  lower_le := by
    intro x hx
    have he : x = L.first := by simpa using hx
    exact he.le
  upper_ge := fun x hx => (L.lower_bounds x hx).1
  lower_fresh := by
    intro x hx
    have he : x = L.first := by simpa using hx
    subst x
    exact L.lower_fresh L.first L.first_lower
  upper_fresh := L.lower_fresh
  marker_fresh := L.marker_fresh

/-- The same common first index for the full upper label. -/
def first_to_upper {H : Set ℕ} {B n c : ℕ} (L : DoubleOverlapLabels H B n c) :
    LastFirstLabels H B 1 c where
  lower := {L.first}
  upper := L.upper
  pivot := L.first
  marker := L.marker
  lower_card := by simp
  upper_card := L.upper_card
  pivot_lower := by simp
  pivot_upper := L.first_upper
  lower_le := by
    intro x hx
    have he : x = L.first := by simpa using hx
    exact he.le
  upper_ge := by
    intro x hx
    rcases L.upper_bounds x hx with rfl | hle
    · exact le_rfl
    · exact L.first_lt_pivot.le.trans hle
  lower_fresh := by
    intro x hx
    have he : x = L.first := by simpa using hx
    subst x
    exact L.upper_fresh L.first L.first_upper
  upper_fresh := L.upper_fresh
  marker_fresh := L.marker_fresh

#print axioms exists_of_infinite
#print axioms exists_sizes_of_infinite
#print axioms intersection

end DoubleOverlapLabels

end Erdos591.Positive.Game

end Erdos118.Reused591
