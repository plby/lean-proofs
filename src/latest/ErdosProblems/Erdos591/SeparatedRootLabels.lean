import ErdosProblems.Erdos591.SplicedRootLabels

/-!
# Only the first upper root index is shared

For the nonlast case with upper critical body rank one, every later
upper selected body lies strictly beyond the largest lower selected
body. Erasing the upper anchor from a rank-two splice gives this
pattern without changing any lower selected index.
-/

namespace Erdos591.Positive.Game

structure SeparatedRootLabels (H : Set ℕ) (B e d j : ℕ) where
  lower : Finset ℕ
  upper : Finset ℕ
  first : ℕ
  last : ℕ
  marker : ℕ
  lower_card : lower.card = e
  upper_card : upper.card = d
  first_lower : first ∈ lower
  first_upper : first ∈ upper
  first_rank : (lower.filter (fun x => x ≤ first)).card = j
  lower_sup : lower.sup id = last
  upper_first : ∀ x ∈ upper, first ≤ x
  upper_after : ∀ x ∈ upper, x = first ∨ last < x
  lower_fresh : ∀ x ∈ lower, x ∈ H ∧ B < x ∧ x < marker
  upper_fresh : ∀ x ∈ upper, x ∈ H ∧ B < x ∧ x < marker
  marker_fresh : marker ∈ H ∧ B < marker

namespace SeparatedRootLabels

theorem exists_of_infinite {H : Set ℕ} (hH : H.Infinite) (B e d j : ℕ)
    (hj : 0 < j) (hje : j < e) (hd : 2 ≤ d) :
    Nonempty (SeparatedRootLabels H B e d j) := by
  classical
  obtain ⟨R⟩ := SplicedRootLabels.exists_of_infinite hH B e (d + 1) j 2 hj hje le_rfl (by omega)
  have hpair : {R.first, R.anchor} = R.upper.filter (fun x => x ≤ R.anchor) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_filter.mpr ⟨R.first_upper, R.first_lt_anchor.le⟩
      · rw [Finset.mem_singleton.mp hx]
        exact Finset.mem_filter.mpr ⟨R.anchor_upper, le_rfl⟩
    · rw [R.anchor_upper_rank]
      simp [R.first_lt_anchor.ne]
  refine ⟨⟨R.lower, R.upper.erase R.anchor, R.first, R.last, R.marker, R.lower_card, ?_,
    R.first_lower, Finset.mem_erase.mpr ⟨R.first_lt_anchor.ne, R.first_upper⟩,
    R.first_rank, R.lower_sup, ?_, ?_, R.lower_fresh, ?_, R.marker_fresh⟩⟩
  · rw [Finset.card_erase_of_mem R.anchor_upper, R.upper_card]
    omega
  · intro x hx
    exact R.upper_first x (Finset.mem_erase.mp hx).2
  · intro x hx
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hx
    rcases R.upper_gap x hmem with hle | hgt
    · have hxpair : x ∈ ({R.first, R.anchor} : Finset ℕ) := by
        rw [hpair]
        exact Finset.mem_filter.mpr ⟨hmem, hle⟩
      have heq : x = R.first ∨ x = R.anchor := by simpa using hxpair
      exact Or.inl (heq.resolve_right hne)
    · exact Or.inr hgt
  · intro x hx
    exact R.upper_fresh x (Finset.mem_erase.mp hx).2

#print axioms exists_of_infinite

end SeparatedRootLabels

end Erdos591.Positive.Game
