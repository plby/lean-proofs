import ErdosProblems.Erdos248.FinalReduction
import ErdosProblems.Erdos248.PrimeSumBounds

/-!
# Erdős Problem 248: assembly of the weighted bad-shift bounds

This file is independent of the analytic derivation of the moment estimates.
It records the exact interface those estimates must satisfy.  A near shift
has a medium-prime and a large-prime exceptional event; a far shift has only
the large-prime event.  The deterministic prime-range decomposition reduces
failure of the desired `omega` bound to their union, and the reciprocal-square
budget makes the sum of their weighted masses strictly smaller than the sieve
mass.
-/

noncomputable section

open scoped ArithmeticFunction.omega BigOperators

namespace Erdos248

local instance badMassAssemblyDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The medium-prime count.  It is used only for `k <= K`. -/
def mediumPrimeCount (K k n : ℕ) : ℕ :=
  omegaBetween (n + k) (tinyCutoff K) (shiftRadius K k)

/-- The lower endpoint of the large-prime range, with the near and far
definitions combined into one expression. -/
def largePrimeLower (K k : ℕ) : ℕ :=
  if k ≤ K then shiftRadius K k else max (tinyCutoff K) k

/-- The large-prime count at an arbitrary relevant shift. -/
def largePrimeCount (K k n : ℕ) : ℕ :=
  omegaBetween (n + k) (largePrimeLower K k) (shiftRadius K 1)

/-- Unnormalized weighted mass of the near medium-prime tail. -/
def mediumPrimeBadMass (K T k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
    if T * k < mediumPrimeCount K k n then sieveWeight K n else 0

/-- Unnormalized weighted mass of the large-prime tail. -/
def largePrimeBadMass (K T k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
    if T * k < largePrimeCount K k n then sieveWeight K n else 0

theorem mediumPrimeBadMass_nonneg (K T k : ℕ) :
    0 ≤ mediumPrimeBadMass K T k := by
  unfold mediumPrimeBadMass
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact sieveWeight_nonneg K n
  · exact le_rfl

theorem largePrimeBadMass_nonneg (K T k : ℕ) :
    0 ≤ largePrimeBadMass K T k := by
  unfold largePrimeBadMass
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact sieveWeight_nonneg K n
  · exact le_rfl

@[simp] theorem largePrimeLower_of_le {K k : ℕ} (hk : k ≤ K) :
    largePrimeLower K k = shiftRadius K k := by
  simp [largePrimeLower, hk]

@[simp] theorem largePrimeLower_of_lt {K k : ℕ} (hk : K < k) :
    largePrimeLower K k = max (tinyCutoff K) k := by
  simp [largePrimeLower, not_le_of_gt hk]

/-- Pointwise deterministic reduction at a near shift. -/
theorem natBadAt_near_imp_medium_or_large
    {K C T k n : ℕ} (hK : 0 < K) (hC : 2 * T + 102 ≤ C)
    (hk1 : 1 ≤ k) (hkK : k ≤ K)
    (hnlow : intervalStart K ≤ n) (hnhigh : n < 2 * intervalStart K)
    (hnweight : sieveWeight K n ≠ 0) (hbad : natBadAt C k n) :
    T * k < mediumPrimeCount K k n ∨ T * k < largePrimeCount K k n := by
  have homega := omega_near_le_deterministic_add_ranges hK hk1 hkK
    hnlow hnhigh hnweight
  simp only [mediumPrimeCount, largePrimeCount, largePrimeLower_of_le hkK]
  by_contra hnot
  push Not at hnot
  unfold natBadAt at hbad
  have hCle : (2 * T + 102) * k ≤ C * k := Nat.mul_le_mul_right k hC
  have hbound : ω (n + k) ≤ (2 * T + 102) * k := by
    nlinarith
  exact (not_lt_of_ge (hbound.trans hCle)) hbad

/-- Pointwise deterministic reduction at a far shift. -/
theorem natBadAt_far_imp_large
    {K C T k n : ℕ} (hK : 0 < K) (hC : 2 * T + 102 ≤ C)
    (hk1 : 1 ≤ k) (hkK : K < k) (hkM : k ≤ intervalExponent K)
    (hnlow : intervalStart K ≤ n) (hnhigh : n < 2 * intervalStart K)
    (hnweight : sieveWeight K n ≠ 0) (hbad : natBadAt C k n) :
    T * k < largePrimeCount K k n := by
  have homega := omega_far_le_deterministic_add_range hK hk1 hkM
    hnlow hnhigh hnweight
  simp only [largePrimeCount, largePrimeLower_of_lt hkK]
  by_contra hnot
  push Not at hnot
  unfold natBadAt at hbad
  have hTle : T + 102 ≤ 2 * T + 102 := by omega
  have hCle : (T + 102) * k ≤ C * k :=
    (Nat.mul_le_mul_right k hTle).trans (Nat.mul_le_mul_right k hC)
  have hbound : ω (n + k) ≤ (T + 102) * k := by
    nlinarith
  exact (not_lt_of_ge (hbound.trans hCle)) hbad

/-- Weighted union bound at one relevant shift. -/
theorem weightedBadMass_le_primeRangeBadMasses
    {K C T k : ℕ} (hK : 0 < K) (hC : 2 * T + 102 ≤ C)
    (hk1 : 1 ≤ k) (hkM : k ≤ intervalExponent K) :
    weightedBadMass K C k ≤
      largePrimeBadMass K T k +
        (if k ≤ K then mediumPrimeBadMass K T k else 0) := by
  by_cases hkK : k ≤ K
  · rw [if_pos hkK]
    unfold weightedBadMass largePrimeBadMass mediumPrimeBadMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    have hnrange := Finset.mem_Ico.mp hn
    by_cases hw : sieveWeight K n = 0
    · simp [hw]
    by_cases hbad : natBadAt C k n
    · rw [if_pos hbad]
      have hor := natBadAt_near_imp_medium_or_large hK hC hk1 hkK
        hnrange.1 hnrange.2 hw hbad
      rcases hor with hmed | hlarge
      · simp only [if_pos hmed, le_add_iff_nonneg_left]
        split_ifs
        · exact sieveWeight_nonneg K n
        · exact le_rfl
      · simp only [if_pos hlarge, le_add_iff_nonneg_right]
        split_ifs
        · exact sieveWeight_nonneg K n
        · exact le_rfl
    · rw [if_neg hbad]
      apply add_nonneg
      · split_ifs
        · exact sieveWeight_nonneg K n
        · exact le_rfl
      · split_ifs
        · exact sieveWeight_nonneg K n
        · exact le_rfl
  · rw [if_neg hkK, add_zero]
    unfold weightedBadMass largePrimeBadMass
    apply Finset.sum_le_sum
    intro n hn
    have hnrange := Finset.mem_Ico.mp hn
    by_cases hw : sieveWeight K n = 0
    · simp [hw]
    by_cases hbad : natBadAt C k n
    · rw [if_pos hbad]
      have hkK' : K < k := Nat.lt_of_not_ge hkK
      have hlarge := natBadAt_far_imp_large hK hC hk1 hkK' hkM
        hnrange.1 hnrange.2 hw hbad
      simp [hlarge]
    · rw [if_neg hbad]
      split_ifs
      · exact sieveWeight_nonneg K n
      · exact le_rfl

/-- The final summable-tail interface.  Each of the two analytic exceptional
events receives `1/(16 k^2)` of the total mass. -/
theorem uniform_weightedBadMass_of_primeRange_tails
    {A : ℝ} (hA : HasUniformWirsingBound A)
    {K C T : ℕ} (hreg : NormalizationRegular A K)
    (hC : 2 * T + 102 ≤ C)
    (hmedium : ∀ k, 1 ≤ k → k ≤ K →
      mediumPrimeBadMass K T k ≤
        sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2)))
    (hlarge : ∀ k, 1 ≤ k → k ≤ intervalExponent K →
      largePrimeBadMass K T k ≤
        sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) :
    (∑ k ∈ Finset.Icc 1 (intervalExponent K), weightedBadMass K C k) <
      sieveMass K := by
  have hmass : 0 < sieveMass K := sieveMass_pos hA hreg
  have hpoint : ∀ k ∈ Finset.Icc 1 (intervalExponent K),
      weightedBadMass K C k ≤
        2 * (sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hraw := weightedBadMass_le_primeRangeBadMasses hreg.1 hC hk'.1 hk'.2
    by_cases hkK : k ≤ K
    · rw [if_pos hkK] at hraw
      calc
        weightedBadMass K C k ≤
            largePrimeBadMass K T k + mediumPrimeBadMass K T k := hraw
        _ ≤ sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2)) +
            sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2)) :=
          add_le_add (hlarge k hk'.1 hk'.2) (hmedium k hk'.1 hkK)
        _ = 2 * (sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) := by ring
    · rw [if_neg hkK, add_zero] at hraw
      calc
        weightedBadMass K C k ≤ largePrimeBadMass K T k := hraw
        _ ≤ sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2)) :=
          hlarge k hk'.1 hk'.2
        _ ≤ 2 * (sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) := by
          have : 0 ≤ sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2)) := by
            positivity
          linarith
  calc
    (∑ k ∈ Finset.Icc 1 (intervalExponent K), weightedBadMass K C k) ≤
        ∑ k ∈ Finset.Icc 1 (intervalExponent K),
          2 * (sieveMass K * ((1 : ℝ) / (16 * (k : ℝ) ^ 2))) := by
      exact Finset.sum_le_sum hpoint
    _ = (sieveMass K / 8) *
        (∑ k ∈ Finset.Icc 1 (intervalExponent K),
          (1 : ℝ) / (k : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (sieveMass K / 8) * 2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_Icc_one_div_sq_le_two (intervalExponent K)) (by positivity)
    _ < sieveMass K := by
      nlinarith

end Erdos248
