import ErdosProblems.Erdos591.OverlapLabels

/-!
# A common first leaf, followed by a lower second / upper last leaf

The strict ending needs beta, then the SU interiors, then gamma, then
the ST interiors. Thus gamma is the second ST selection and the last
SU selection; it is not a common last selection. The earlier common-last
label pattern remains available unchanged for the aligned construction.
-/

namespace Erdos591.Positive.Game

structure FirstSecondLastLabels (H : Set ℕ) (B p q : ℕ) where
  lower : Finset ℕ
  upper : Finset ℕ
  first : ℕ
  pivot : ℕ
  marker : ℕ
  lower_card : lower.card = p
  upper_card : upper.card = q
  first_lower : first ∈ lower
  first_upper : first ∈ upper
  pivot_lower : pivot ∈ lower
  pivot_upper : pivot ∈ upper
  first_lt_pivot : first < pivot
  lower_first : ∀ x ∈ lower, first ≤ x
  lower_gap : ∀ x ∈ lower, x = first ∨ pivot ≤ x
  upper_bounds : ∀ x ∈ upper, first ≤ x ∧ x ≤ pivot
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < marker
  upper_fresh : ∀ x ∈ upper, x ∈ H ∧ B < x ∧ x < marker
  marker_fresh : marker ∈ H ∧ B < marker

namespace FirstSecondLastLabels

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B p q : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) : Nonempty (FirstSecondLastLabels H B p q) := by
  classical
  obtain ⟨f, _hf, hfH, hfB, _⟩ :=
    FastSequence.exists_above_finite_bounds hH ∅ (fun _ => B)
  obtain ⟨L⟩ := LastFirstLabels.exists_of_infinite hH (f 0) (q - 1) (p - 1)
    (by omega) (by omega)
  have hfirstLower : f 0 ∉ L.lower := fun h => Nat.lt_irrefl _ (L.lower_fresh _ h).2.1
  have hfirstUpper : f 0 ∉ L.upper := fun h => Nat.lt_irrefl _ (L.upper_fresh _ h).2.1
  have hfirstPivot := (L.lower_fresh _ L.pivot_lower).2.1
  refine ⟨⟨insert (f 0) L.upper, insert (f 0) L.lower, f 0, L.pivot, L.marker,
    ?_, ?_, by simp, by simp, Finset.mem_insert_of_mem L.pivot_upper,
    Finset.mem_insert_of_mem L.pivot_lower, hfirstPivot, ?_, ?_, ?_, ?_, ?_,
    ⟨L.marker_fresh.1, (hfB 0).trans L.marker_fresh.2⟩⟩⟩
  · rw [Finset.card_insert_of_notMem hfirstUpper, L.upper_card]
    omega
  · rw [Finset.card_insert_of_notMem hfirstLower, L.lower_card]
    omega
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact (L.upper_fresh x hx).2.1.le
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (L.upper_ge x hx)
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨le_rfl, hfirstPivot.le⟩
    · exact ⟨(L.lower_fresh x hx).2.1.le, L.lower_le x hx⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hfH 0, hfB 0, L.marker_fresh.2⟩
    · have h := L.upper_fresh x hx
      exact ⟨h.1, (hfB 0).trans h.2.1, h.2.2⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨hfH 0, hfB 0, L.marker_fresh.2⟩
    · have h := L.lower_fresh x hx
      exact ⟨h.1, (hfB 0).trans h.2.1, h.2.2⟩

variable {H : Set ℕ} {B p q : ℕ}

def first_to_lower (L : FirstSecondLastLabels H B p q) : LastFirstLabels H B 1 p where
  lower := {L.first}
  upper := L.lower
  pivot := L.first
  marker := L.marker
  lower_card := by simp
  upper_card := L.lower_card
  pivot_lower := by simp
  pivot_upper := L.first_lower
  lower_le := fun _ hx => (Finset.mem_singleton.mp hx).le
  upper_ge := L.lower_first
  lower_fresh := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact L.lower_fresh _ L.first_lower
  upper_fresh := L.lower_fresh
  marker_fresh := L.marker_fresh

def first_to_upper (L : FirstSecondLastLabels H B p q) : LastFirstLabels H B 1 q where
  lower := {L.first}
  upper := L.upper
  pivot := L.first
  marker := L.marker
  lower_card := by simp
  upper_card := L.upper_card
  pivot_lower := by simp
  pivot_upper := L.first_upper
  lower_le := fun _ hx => (Finset.mem_singleton.mp hx).le
  upper_ge := fun x hx => (L.upper_bounds x hx).1
  lower_fresh := by
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact L.upper_fresh _ L.first_upper
  upper_fresh := L.upper_fresh
  marker_fresh := L.marker_fresh

theorem pivot_next_lower (L : FirstSecondLastLabels H B p q) (x : ℕ)
    (hx : x ∈ L.lower) (hgt : L.first < x) : L.pivot ≤ x :=
  (L.lower_gap x hx).resolve_left hgt.ne'

theorem upper_sup (L : FirstSecondLastLabels H B p q) : L.upper.sup id = L.pivot :=
  le_antisymm (Finset.sup_le fun x hx => (L.upper_bounds x hx).2)
    (Finset.le_sup (f := id) L.pivot_upper)

#print axioms exists_of_infinite

end FirstSecondLastLabels

end Erdos591.Positive.Game
