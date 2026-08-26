/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralSingularSeries

/-!
# Quantitative bounds for inverse singular-series losses

This file turns the local support statement in `GeneralSingularSeries` into
the finite Bonferroni lower bound used before averaging over the auxiliary
prime.  No asymptotic estimate is used here.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

/-- The local inverse-factor loss is bounded by its worst value at
multiplicity zero. -/
theorem largeGapLocalPenalty_le_dimension_ratio
    {H : Finset ℕ} {m q p : ℕ} (hKp : 2 * H.card < p) :
    largeGapLocalPenalty H m q p ≤
      ((2 * H.card : ℕ) : ℝ) / ((p : ℝ) - 2 * H.card) := by
  have homega := largeGapLocalMultiplicity_le_two_mul_card H m q p
  have homegaR :
      (largeGapLocalMultiplicity H m q p : ℝ) ≤
        ((2 * H.card : ℕ) : ℝ) := by
    exact_mod_cast homega
  have hnum : 0 ≤
      ((2 * H.card : ℕ) : ℝ) -
        largeGapLocalMultiplicity H m q p := sub_nonneg.mpr homegaR
  have hnumLe :
      ((2 * H.card : ℕ) : ℝ) -
          largeGapLocalMultiplicity H m q p ≤
        ((2 * H.card : ℕ) : ℝ) := by
    exact sub_le_self _ (Nat.cast_nonneg _)
  have hden : 0 < (p : ℝ) - 2 * H.card := by
    exact sub_pos.mpr (by exact_mod_cast hKp)
  have hdenLe :
      (p : ℝ) - 2 * (H.card : ℝ) ≤
        (p : ℝ) - largeGapLocalMultiplicity H m q p := by
    norm_num [Nat.cast_mul] at homegaR
    linarith
  unfold largeGapLocalPenalty
  exact div_le_div₀ (Nat.cast_nonneg _) hnumLe hden hdenLe

/-- Once the prime is at least twice the doubled dimension, the loss is at
most `4K/p`. -/
theorem largeGapLocalPenalty_le_four_mul_card_div
    {H : Finset ℕ} {m q p : ℕ} (hp : p.Prime)
    (hfour : 4 * H.card ≤ p) :
    largeGapLocalPenalty H m q p ≤
      (4 * H.card : ℕ) / (p : ℝ) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have htwo : 2 * H.card < p := by
    by_cases hK : H.card = 0
    · simp [hK, hp.pos]
    · have hKpos : 0 < H.card := Nat.pos_of_ne_zero hK
      omega
  have hden : (0 : ℝ) < (p : ℝ) - 2 * H.card := by
    exact sub_pos.mpr (by exact_mod_cast htwo)
  have hfourR : ((4 * H.card : ℕ) : ℝ) ≤ p := by
    exact_mod_cast hfour
  calc
    largeGapLocalPenalty H m q p ≤
        ((2 * H.card : ℕ) : ℝ) / ((p : ℝ) - 2 * H.card) :=
      largeGapLocalPenalty_le_dimension_ratio htwo
    _ ≤ ((4 * H.card : ℕ) : ℝ) / p := by
      rw [div_le_div_iff₀ hden hpPos]
      push_cast at hfourR ⊢
      nlinarith

/-- Rough primes on which the inverse singular factor is genuinely changed.
-/
def largeGapRoughPenaltyPrimes
    (H : Finset ℕ) (m q w y : ℕ) : Finset ℕ :=
  (Nat.primesLE y).filter fun p ↦
    w < p ∧ largeGapLocalPenalty H m q p ≠ 0

/-- A convenient divisibility superset of the genuine penalty support. -/
def largeGapRoughExceptionalPrimes
    (K w m q y : ℕ) : Finset ℕ :=
  (Nat.primesLE y).filter fun p ↦
    w < p ∧
      p ∣ q * m *
        crossExceptionalModulus (preSievedShifts K w) m q

theorem largeGapRoughPenaltyPrimes_subset_exceptional
    {K w m q y : ℕ} (hKw : 2 * K ≤ w) :
    largeGapRoughPenaltyPrimes (preSievedShifts K w) m q w y ⊆
      largeGapRoughExceptionalPrimes K w m q y := by
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpPrime := (Nat.mem_primesLE.mp hpData.1).2
  have hsupport :=
    prime_dvd_q_or_m_or_crossExceptional_of_localPenalty_ne_zero
      hpPrime hKw hpData.2.1 hpData.2.2
  apply Finset.mem_filter.mpr
  refine ⟨hpData.1, hpData.2.1, ?_⟩
  rcases hsupport with hpq | hpm | hpex
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpq m) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpm q) _
  · exact dvd_mul_of_dvd_right hpex (q * m)

/-- The sum of all rough local losses is bounded by the reciprocal mass of
the explicit exceptional-prime support. -/
theorem sum_largeGapRoughPenaltyPrimes_le_exceptionalReciprocalMass
    {K w m q y : ℕ} (hfour : 4 * K ≤ w) :
    (∑ p ∈ largeGapRoughPenaltyPrimes
        (preSievedShifts K w) m q w y,
      largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
      (4 * K : ℕ) *
        ∑ p ∈ largeGapRoughExceptionalPrimes K w m q y,
          (p : ℝ)⁻¹ := by
  have hKw : 2 * K ≤ w := by omega
  have hsubset := largeGapRoughPenaltyPrimes_subset_exceptional
    (m := m) (q := q) (y := y) hKw
  calc
    (∑ p ∈ largeGapRoughPenaltyPrimes
        (preSievedShifts K w) m q w y,
      largeGapLocalPenalty (preSievedShifts K w) m q p) ≤
        ∑ p ∈ largeGapRoughPenaltyPrimes
            (preSievedShifts K w) m q w y,
          ((4 * K : ℕ) : ℝ) / p := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := Finset.mem_filter.mp hp
      have hpPrime := (Nat.mem_primesLE.mp hpData.1).2
      have hfourp : 4 * (preSievedShifts K w).card ≤ p := by
        rw [card_preSievedShifts]
        omega
      simpa only [card_preSievedShifts] using
        (largeGapLocalPenalty_le_four_mul_card_div
          (H := preSievedShifts K w) (m := m) (q := q) hpPrime hfourp)
    _ ≤ ∑ p ∈ largeGapRoughExceptionalPrimes K w m q y,
          ((4 * K : ℕ) : ℝ) / p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp hpnot
      positivity
    _ = ((4 * K : ℕ) : ℝ) *
        ∑ p ∈ largeGapRoughExceptionalPrimes K w m q y,
          (p : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [div_eq_mul_inv]

/-- The rough amplification product has the desired first-order
Bonferroni lower bound.  Its only remaining analytic input is now the
average reciprocal mass of the displayed exceptional prime set. -/
theorem one_sub_exceptionalReciprocalMass_le_roughAmplificationInverse
    {K w m q y : ℕ} (hfour : 4 * K ≤ w) :
    1 - ((4 * K : ℕ) : ℝ) *
        (∑ p ∈ largeGapRoughExceptionalPrimes K w m q y,
          (p : ℝ)⁻¹) ≤
      ∏ p ∈ largeGapRoughPenaltyPrimes
          (preSievedShifts K w) m q w y,
        (largeGapLocalAmplification
          (preSievedShifts K w) m q p)⁻¹ := by
  have hsum :=
    sum_largeGapRoughPenaltyPrimes_le_exceptionalReciprocalMass
      (m := m) (q := q) (y := y) hfour
  have hlarge : ∀ p ∈ largeGapRoughPenaltyPrimes
      (preSievedShifts K w) m q w y,
      2 * (preSievedShifts K w).card < p := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    rw [card_preSievedShifts]
    omega
  calc
    1 - ((4 * K : ℕ) : ℝ) *
        (∑ p ∈ largeGapRoughExceptionalPrimes K w m q y,
          (p : ℝ)⁻¹) ≤
        1 - ∑ p ∈ largeGapRoughPenaltyPrimes
          (preSievedShifts K w) m q w y,
          largeGapLocalPenalty (preSievedShifts K w) m q p :=
      sub_le_sub_left hsum 1
    _ ≤ _ := one_sub_sum_largeGapLocalPenalty_le_prod_amplification_inv
      _ hlarge

end

end Erdos4b
