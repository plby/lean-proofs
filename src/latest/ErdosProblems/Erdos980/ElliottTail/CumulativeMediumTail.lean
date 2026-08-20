import ErdosProblems.Erdos980.ElliottTail.Definitions

/-!
# Cumulative-count control of Elliott's medium tail

The analytic sieve naturally bounds the cumulative event that the least
nonresidue exceeds a numerical cutoff.  This file converts such bounds into
the weighted medium-tail estimate by the finite layer-cake identity.
-/

namespace Erdos980.ElliottTail

open scoped BigOperators

noncomputable section

private lemma nat_eq_succ_add_card_Ico_filter
    {y Y n : ℕ} (hyn : y < n) (hnY : n ≤ Y) :
    n = y + 1 + ((Finset.Ico (y + 1) Y).filter (fun t ↦ t < n)).card := by
  have hfilter :
      (Finset.Ico (y + 1) Y).filter (fun t ↦ t < n) =
        Finset.Ico (y + 1) n := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hfilter]
  simp only [Nat.card_Ico]
  omega

/-- Finite layer-cake identity for a family of natural-valued weights in
the interval `(y,Y]`. -/
theorem sum_nat_eq_layerCake
    {α : Type*} (S : Finset α) (n : α → ℕ) (y Y : ℕ)
    (hlower : ∀ a ∈ S, y < n a) (hupper : ∀ a ∈ S, n a ≤ Y) :
    (∑ a ∈ S, (n a : ℝ)) =
      (y + 1 : ℝ) * S.card +
        ∑ t ∈ Finset.Ico (y + 1) Y,
          ((S.filter (fun a ↦ t < n a)).card : ℝ) := by
  classical
  calc
    (∑ a ∈ S, (n a : ℝ)) =
        ∑ a ∈ S,
          (((y + 1 : ℕ) +
            ((Finset.Ico (y + 1) Y).filter (fun t ↦ t < n a)).card : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      norm_cast
      exact nat_eq_succ_add_card_Ico_filter (hlower a ha) (hupper a ha)
    _ = ∑ a ∈ S, ((y + 1 : ℕ) : ℝ) +
          ∑ a ∈ S,
            (((Finset.Ico (y + 1) Y).filter (fun t ↦ t < n a)).card : ℝ) := by
      simp only [Nat.cast_add, Finset.sum_add_distrib]
    _ = (y + 1 : ℝ) * S.card +
          ∑ a ∈ S,
            (((Finset.Ico (y + 1) Y).filter (fun t ↦ t < n a)).card : ℝ) := by
      congr 1
      simp [nsmul_eq_mul]
      ring
    _ = (y + 1 : ℝ) * S.card +
          ∑ a ∈ S, ∑ t ∈ Finset.Ico (y + 1) Y,
            if t < n a then (1 : ℝ) else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = (y + 1 : ℝ) * S.card +
          ∑ t ∈ Finset.Ico (y + 1) Y, ∑ a ∈ S,
            if t < n a then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = (y + 1 : ℝ) * S.card +
          ∑ t ∈ Finset.Ico (y + 1) Y,
            ((S.filter (fun a ↦ t < n a)).card : ℝ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      simp

/-- Exact cumulative-count expansion of the unnormalized medium tail. -/
theorem mediumWeightedTailSum_eq_layerCake
    (k y Y x : ℕ) :
    mediumWeightedTailSum k y Y x =
      (y + 1 : ℝ) *
          ((primesBelow x).filter
            (fun p ↦ y < leastKthPowerNonresidue k p ∧
              leastKthPowerNonresidue k p ≤ Y)).card +
        ∑ t ∈ Finset.Ico (y + 1) Y,
          ((((primesBelow x).filter
              (fun p ↦ y < leastKthPowerNonresidue k p ∧
                leastKthPowerNonresidue k p ≤ Y)).filter
            (fun p ↦ t < leastKthPowerNonresidue k p)).card : ℝ) := by
  unfold mediumWeightedTailSum
  exact sum_nat_eq_layerCake _ _ y Y
    (fun _ hp ↦ (Finset.mem_filter.mp hp).2.1)
    (fun _ hp ↦ (Finset.mem_filter.mp hp).2.2)

/-- The layer-cake identity bounded by the full cumulative exceptional
sets.  This is the direct bridge used by numerical-cutoff sieve estimates. -/
theorem mediumWeightedTailSum_le_cumulativeExceptional
    (k y Y x : ℕ) :
    mediumWeightedTailSum k y Y x ≤
      (y + 1 : ℝ) * (exceptionalPrimes k y x).card +
        ∑ t ∈ Finset.Ico (y + 1) Y,
          ((exceptionalPrimes k t x).card : ℝ) := by
  classical
  rw [mediumWeightedTailSum_eq_layerCake]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact_mod_cast Finset.card_le_card (by
      intro p hp
      have hpmed := Finset.mem_filter.mp hp
      have hpbase : p < x ∧ p.Prime := by
        simpa [primesBelow] using hpmed.1
      exact mem_exceptionalPrimes.mpr
        ⟨hpbase.1, hpbase.2, hpmed.2.1⟩)
  · apply Finset.sum_le_sum
    intro t ht
    exact_mod_cast Finset.card_le_card (by
      intro p hp
      have hpt := Finset.mem_filter.mp hp
      have hpmed := Finset.mem_filter.mp hpt.1
      have hpbase : p < x ∧ p.Prime := by
        simpa [primesBelow] using hpmed.1
      exact mem_exceptionalPrimes.mpr
        ⟨hpbase.1, hpbase.2, hpt.2⟩)

end

end Erdos980.ElliottTail
