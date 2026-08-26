/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.LargeAnchorMass
import ErdosProblems.Erdos822.LargeDivisorRigidity
import ErdosProblems.Erdos822.CofactorRepresentation
import ErdosProblems.Erdos822.LargeCutoffB4

/-! # Global gcd mass in the large common-divisor range -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

noncomputable def largeAboveAnchor (N S : ℕ) (C : ℝ) (m' : ℕ) : Finset ℕ :=
  (gilCofactors N S C).filter fun m ↦ m' < m ∧
    (outerCollisionPairs (N ^ 60) m m').Nonempty ∧
    N ^ 20 < shiftedCoefficientGcd m m'

theorem largeAboveAnchor_subset_sameInner_image {N S k r q' : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (ht' : (k, r, q') ∈ oddCofactorTriples N) :
    largeAboveAnchor N S C (k * r * q') ⊆
      (sameInnerSupportedPrimes N S C (k * r) q').image (fun q ↦ k * r * q) := by
  intro m hm
  obtain ⟨hmG, hlt, hne, hlarge⟩ := Finset.mem_filter.mp hm
  obtain ⟨k₁, r₁, q, hk₁, hr₁, hq, rfl⟩ :=
    exists_oddCofactorTriple_of_mem_oddRaw (gilCofactors_subset_oddRaw N S C hmG)
  have ht : (k₁, r₁, q) ∈ oddCofactorTriples N :=
    mem_oddCofactorTriples_iff.mpr ⟨hk₁, hr₁, hq⟩
  obtain ⟨rfl, rfl⟩ := inner_factors_eq_of_large_supported_gcd hN ht ht' hne hlarge
  refine Finset.mem_image.mpr ⟨q, ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨hq, Nat.lt_of_mul_lt_mul_left hlt, hmG, hne⟩

theorem sum_largeAboveAnchor_gcd_div_le {N S k r q' : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N)
    (ht' : (k, r, q') ∈ oddCofactorTriples N)
    (hm' : k * r * q' ∈ gilCofactors N S C) :
    (∑ m ∈ largeAboveAnchor N S C (k * r * q'),
      (shiftedCoefficientGcd m (k * r * q') : ℝ) / m) ≤
      23 * N * (harmonic N : ℝ) *
        (roughPart (shiftedTotient (k * r * q')) (b1Cutoff N)).divisors.card / (k * r : ℕ) := by
  have hdata := mem_oddCofactorTriples_iff.mp ht'
  have hl : 0 < k * r := mul_pos (oddSmallFactors_pos hdata.1)
    (mem_middlePrimes_iff.mp hdata.2.1).2.2.pos
  calc
    _ ≤ ∑ m ∈ (sameInnerSupportedPrimes N S C (k * r) q').image (fun q ↦ k * r * q),
        (shiftedCoefficientGcd m (k * r * q') : ℝ) / m :=
      Finset.sum_le_sum_of_subset_of_nonneg (largeAboveAnchor_subset_sameInner_image hN ht')
        (fun m hm hnot ↦ by positivity)
    _ = ∑ q ∈ sameInnerSupportedPrimes N S C (k * r) q',
        (shiftedCoefficientGcd (k * r * q) (k * r * q') : ℝ) / (k * r * q : ℕ) := by
      rw [Finset.sum_image]
      intro a ha b hb heq
      exact Nat.eq_of_mul_eq_mul_left hl heq
    _ ≤ _ := sum_sameInnerSupportedPrimes_gcd_weight_le hN hy hl hm'

theorem sum_largeAboveAnchor_weight_le {N S k r q' : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N)
    (ht' : (k, r, q') ∈ oddCofactorTriples N)
    (hm' : k * r * q' ∈ gilCofactors N S C)
    (hcard : (roughPart (shiftedTotient (k * r * q')) (b1Cutoff N)).divisors.card ≤ N) :
    (∑ m ∈ largeAboveAnchor N S C (k * r * q'),
      (shiftedCoefficientGcd m (k * r * q') : ℝ) / (m * (k * r * q') : ℕ)) ≤
      23 * (N : ℝ) ^ 3 * ((1 : ℝ) / k) * ((1 : ℝ) / (r ^ 2 : ℕ)) * ((1 : ℝ) / q') := by
  have hk : 0 < k := oddSmallFactors_pos (mem_oddCofactorTriples_iff.mp ht').1
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hbound := sum_largeAboveAnchor_gcd_div_le hN hy ht' hm'
  have hH := harmonic_le_natCast N
  have hc : ((roughPart (shiftedTotient (k * r * q')) (b1Cutoff N)).divisors.card : ℝ) ≤ N :=
    by exact_mod_cast hcard
  have hcoef : 23 * N * (harmonic N : ℝ) *
      (roughPart (shiftedTotient (k * r * q')) (b1Cutoff N)).divisors.card ≤ 23 * (N : ℝ) ^ 3 := by
    calc
      _ ≤ 23 * (N : ℝ) * N * N :=
        mul_le_mul (mul_le_mul_of_nonneg_left hH (by positivity)) hc (by positivity) (by positivity)
      _ = _ := by ring
  calc
    _ = (1 : ℝ) / (k * r * q' : ℕ) *
        ∑ m ∈ largeAboveAnchor N S C (k * r * q'),
          (shiftedCoefficientGcd m (k * r * q') : ℝ) / m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      push_cast
      ring
    _ ≤ (1 : ℝ) / (k * r * q' : ℕ) *
        (23 * (N : ℝ) ^ 3 / (k * r : ℕ)) :=
      mul_le_mul_of_nonneg_left
        (hbound.trans (div_le_div_of_nonneg_right hcoef (by positivity))) (by positivity)
    _ = (23 * (N : ℝ) ^ 3 * ((1 : ℝ) / k) *
        ((1 : ℝ) / (r ^ 2 : ℕ)) * ((1 : ℝ) / q')) / k := by
      push_cast
      ring
    _ ≤ _ := div_le_self (by positivity) hkR

#print axioms sum_largeAboveAnchor_weight_le

theorem eventually_sum_largeAboveAnchor_weight_le (S : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m' ∈ gilCofactors N S C, ∑ m ∈ largeAboveAnchor N S C m',
        (shiftedCoefficientGcd m m' : ℝ) / (m * m' : ℕ)) ≤ 23 := by
  filter_upwards [eventually_ge_atTop 2, tendsto_b1Cutoff_atTop.eventually_ge_atTop 1,
    eventually_gilCofactors_rough_divisors_card_le S C,
    eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_upper_one]
    with N hN hy hcard hQone
  have hQ : (∑ q ∈ largePrimes N, (1 : ℝ) / q) ≤ 1 := by
    simpa [reciprocalPrimeIntervalSum, largePrimes_eq_primesLE_sdiff] using hQone
  have hK := (sum_inv_oddSmallFactors_le_harmonic N).trans (harmonic_le_natCast N)
  have hR := sum_inv_sq_middlePrimes_le_inv_pow_four hN
  rw [sum_subset_oddRawCofactors_eq_triple_if hN (gilCofactors_subset_oddRaw N S C)]
  calc
    _ ≤ ∑ k ∈ oddSmallFactors N, ∑ r ∈ middlePrimes N, ∑ q' ∈ largePrimes N,
        23 * (N : ℝ) ^ 3 * ((1 : ℝ) / k) * ((1 : ℝ) / (r ^ 2 : ℕ)) * ((1 : ℝ) / q') := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro q' hq'
      split_ifs with hm'
      · exact sum_largeAboveAnchor_weight_le hN hy
          (mem_oddCofactorTriples_iff.mpr ⟨hk, hr, hq'⟩) hm' (hcard _ hm')
      · positivity
    _ = 23 * (N : ℝ) ^ 3 * (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (∑ r ∈ middlePrimes N, (1 : ℝ) / (r ^ 2 : ℕ)) *
        (∑ q' ∈ largePrimes N, (1 : ℝ) / q') := by
      simp only [mul_assoc]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ ≤ 23 * (N : ℝ) ^ 3 * N * ((1 : ℝ) / (N ^ 4 : ℕ)) * 1 := by
      exact mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hK (by positivity)) hR (by positivity) (by positivity))
        hQ (by positivity) (by positivity)
    _ = 23 := by
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
      push_cast
      field_simp

#print axioms eventually_sum_largeAboveAnchor_weight_le

end Erdos822
