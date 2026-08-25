import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Defs

/-! Finite sums split according to the sign of a real-valued index label. -/

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

/-- If terms with zero label vanish, bounds on the positive and negative
parts add to a bound on the full sum. -/
theorem sum_le_two_mul_of_signed_parts {ι : Type*} (s : Finset ι)
    (label term : ι → ℝ) {L : ℝ}
    (hzero : ∀ i ∈ s, label i = 0 → term i = 0)
    (hpos : (∑ i ∈ s.filter (fun i => 0 < label i), term i) ≤ L)
    (hneg : (∑ i ∈ s.filter (fun i => label i < 0), term i) ≤ L) :
    (∑ i ∈ s, term i) ≤ 2 * L := by
  classical
  have hsum : (∑ i ∈ s, term i) =
      (∑ i ∈ s.filter (fun i => 0 < label i), term i) +
        (∑ i ∈ s.filter (fun i => label i < 0), term i) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rcases lt_trichotomy 0 (label i) with h | h | h
    · simp [h, not_lt_of_ge (le_of_lt h)]
    · simp [← h, hzero i hi h.symm]
    · simp [h, not_lt_of_ge (le_of_lt h)]
  rw [hsum]
  linarith

end Puzzling139335.N4MiddleInvolutions.FaceBounds
