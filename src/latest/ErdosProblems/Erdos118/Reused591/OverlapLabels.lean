import ErdosProblems.Erdos118.Reused591.FastSequence

namespace Erdos118.Reused591

/-!
# Fresh last--first overlapping labels

Two prescribed positive label sizes can be realized on one infinite
input pool with the last lower label equal to the first upper label.
Their only common entry is that pivot. One later marker bounds both
labels strictly, and every chosen number exceeds the prescribed bound.
-/

namespace Erdos591.Positive.Game

structure LastFirstLabels (H : Set ℕ) (B a c : ℕ) where
  lower : Finset ℕ
  upper : Finset ℕ
  pivot : ℕ
  marker : ℕ
  lower_card : lower.card = a
  upper_card : upper.card = c
  pivot_lower : pivot ∈ lower
  pivot_upper : pivot ∈ upper
  lower_le : ∀ x ∈ lower, x ≤ pivot
  upper_ge : ∀ x ∈ upper, pivot ≤ x
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < marker
  upper_fresh : ∀ x ∈ upper, x ∈ H ∧ B < x ∧ x < marker
  marker_fresh : marker ∈ H ∧ B < marker

namespace LastFirstLabels

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B a c : ℕ)
    (ha : 0 < a) (hc : 0 < c) : Nonempty (LastFirstLabels H B a c) := by
  classical
  obtain ⟨f, hmono, hmem, hB, _⟩ :=
    FastSequence.exists_above_finite_bounds hH ∅ (fun _ => B)
  let lower := (Finset.range a).image f
  let upper := (Finset.range c).image (fun j => f (a - 1 + j))
  let pivot := f (a - 1)
  let marker := f (a + c - 1)
  have hinj : Function.Injective (fun j => f (a - 1 + j)) := by
    intro i j hij
    exact Nat.add_left_cancel (hmono.injective hij)
  refine ⟨⟨lower, upper, pivot, marker, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [lower, Finset.card_image_of_injective _ hmono.injective]
  · simp [upper, Finset.card_image_of_injective _ hinj]
  · exact Finset.mem_image.mpr ⟨a - 1, Finset.mem_range.mpr (by omega), rfl⟩
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hc, by simp [pivot]⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' := Finset.mem_range.mp hi
    exact hmono.monotone (by omega)
  · intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact hmono.monotone (Nat.le_add_right _ _)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hi' := Finset.mem_range.mp hi
    exact ⟨hmem i, hB i, hmono (by omega)⟩
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hj' := Finset.mem_range.mp hj
    exact ⟨hmem _, hB _, hmono (by omega)⟩
  · exact ⟨hmem _, hB _⟩

theorem intersection {H : Set ℕ} {B a c : ℕ} (L : LastFirstLabels H B a c) :
    L.lower ∩ L.upper = {L.pivot} := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hu⟩
    exact le_antisymm (L.lower_le x hl) (L.upper_ge x hu)
  · rintro rfl
    exact ⟨L.pivot_lower, L.pivot_upper⟩

theorem lower_sup {H : Set ℕ} {B a c : ℕ} (L : LastFirstLabels H B a c) :
    L.lower.sup id = L.pivot :=
  le_antisymm (Finset.sup_le L.lower_le) (Finset.le_sup (f := id) L.pivot_lower)

theorem label_bounds {H : Set ℕ} {B a c : ℕ} (L : LastFirstLabels H B a c) :
    (∀ x ∈ L.lower, 0 < x ∧ x < L.marker) ∧
      (∀ x ∈ L.upper, 0 < x ∧ x < L.marker) := by
  constructor
  · intro x hx
    exact ⟨(Nat.zero_le B).trans_lt (L.lower_fresh x hx).2.1, (L.lower_fresh x hx).2.2⟩
  · intro x hx
    exact ⟨(Nat.zero_le B).trans_lt (L.upper_fresh x hx).2.1, (L.upper_fresh x hx).2.2⟩

#print axioms exists_of_infinite
#print axioms intersection

end LastFirstLabels

end Erdos591.Positive.Game

end Erdos118.Reused591
