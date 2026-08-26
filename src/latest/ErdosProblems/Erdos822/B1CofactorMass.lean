/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B1GoodSmallFactors

/-! # Lifting the B1 small factors to structured cofactors -/

namespace Erdos822

open Filter
open scoped BigOperators

noncomputable def b1CofactorTriples (N : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (b1GoodSmallFactors N).product ((middlePrimes N).product (largePrimes N))

noncomputable def b1Cofactors (N : ℕ) : Finset ℕ :=
  (b1CofactorTriples N).image cofactorProduct

theorem b1CofactorTriples_subset_odd (N : ℕ) :
    b1CofactorTriples N ⊆ oddCofactorTriples N := by
  intro t ht
  obtain ⟨hk, hrq⟩ := Finset.mem_product.mp ht
  exact Finset.mem_product.mpr
    ⟨b1GoodSmallFactors_subset_oddSmallFactors N hk, hrq⟩

theorem b1Cofactors_subset_oddRaw (N : ℕ) : b1Cofactors N ⊆ oddRawCofactors N :=
  Finset.image_subset_image (b1CofactorTriples_subset_odd N)

theorem mem_b1Cofactors_iff {N m : ℕ} :
    m ∈ b1Cofactors N ↔ ∃ k r q : ℕ,
      k ∈ b1GoodSmallFactors N ∧ r ∈ middlePrimes N ∧ q ∈ largePrimes N ∧
        m = k * r * q := by
  change m ∈ ((b1GoodSmallFactors N) ×ˢ ((middlePrimes N) ×ˢ (largePrimes N))).image
    cofactorProduct ↔ _
  simp only [Finset.mem_image, Prod.exists, Finset.mem_product, cofactorProduct]
  constructor
  · rintro ⟨k, r, q, ⟨hk, hr, hq⟩, hm⟩
    exact ⟨k, r, q, hk, hr, hq, hm.symm⟩
  · rintro ⟨k, r, q, hk, hr, hq, hm⟩
    exact ⟨k, r, q, ⟨hk, hr, hq⟩, hm.symm⟩

theorem sum_inv_b1Cofactors_eq_product {N : ℕ} (hN : 2 ≤ N) :
    (∑ m ∈ b1Cofactors N, (1 : ℝ) / m) =
      (∑ k ∈ b1GoodSmallFactors N, (1 : ℝ) / k) *
        reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) *
          reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) := by
  rw [b1Cofactors, Finset.sum_image
    ((cofactorProduct_injOn_oddCofactorTriples hN).mono (b1CofactorTriples_subset_odd N))]
  rw [b1CofactorTriples]
  change (∑ t ∈ (b1GoodSmallFactors N) ×ˢ ((middlePrimes N) ×ˢ (largePrimes N)),
    (1 : ℝ) / cofactorProduct t) = _
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  rw [middlePrimes_eq_primesLE_sdiff, largePrimes_eq_primesLE_sdiff]
  simp only [reciprocalPrimeIntervalSum, cofactorProduct, Nat.cast_mul, one_div, mul_inv]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

theorem exists_eventually_sum_inv_b1Cofactors_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * Real.log (N : ℝ) ≤ ∑ m ∈ b1Cofactors N, (1 : ℝ) / m := by
  obtain ⟨c, hc, hsmall⟩ := exists_eventually_sum_inv_b1GoodSmallFactors_lower
  refine ⟨c / 500, by positivity, ?_⟩
  filter_upwards [hsmall, eventually_reciprocalPrimeIntervalSum_four_five_lower,
      eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_lower,
      eventually_ge_atTop 2] with N hK hr hq hN
  have hK0 : 0 ≤ ∑ k ∈ b1GoodSmallFactors N, (1 : ℝ) / k :=
    Finset.sum_nonneg fun k hk ↦ by positivity
  have hr0 : 0 ≤ reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) :=
    (by norm_num : (0 : ℝ) ≤ 1 / 10).trans hr
  rw [sum_inv_b1Cofactors_eq_product hN]
  calc
    c / 500 * Real.log (N : ℝ) =
        (c * Real.log (N : ℝ)) * (1 / 10 : ℝ) * (1 / 50 : ℝ) := by ring
    _ ≤ (∑ k ∈ b1GoodSmallFactors N, (1 : ℝ) / k) *
        (1 / 10 : ℝ) * (1 / 50 : ℝ) := by gcongr
    _ ≤ (∑ k ∈ b1GoodSmallFactors N, (1 : ℝ) / k) *
        reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) *
          reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) := by gcongr

theorem b1Cofactors_squareRich {N m : ℕ} (hm : m ∈ b1Cofactors N) :
    TotientSquareRich m (b1Cutoff N) := by
  obtain ⟨k, r, q, hk, hr, hq, rfl⟩ := mem_b1Cofactors_iff.mp hm
  have hkm : k ∣ k * r * q := ⟨r * q, by simp [Nat.mul_assoc]⟩
  intro d hd hdy
  exact (b1GoodSmallFactors_squareRich hk d hd hdy).trans (Nat.totient_dvd_of_dvd hkm)

theorem b1Cofactors_smoothPreserving_of_bounded {N m : ℕ}
    (hm : m ∈ b1Cofactors N) (hbounded : SmallPrimePowersBounded m (b1Cutoff N)) :
    SmoothTotientPreserving m (b1Cutoff N) :=
  smoothTotientPreserving_of_squareRich dvd_rfl (b1Cofactors_squareRich hm) hbounded

theorem b1Cofactors_no_intermediate_prime {N m : ℕ}
    (hN : 2 ≤ N) (hm : m ∈ b1Cofactors N) :
    ∀ p : ℕ, p.Prime → b1Cutoff N < p → p ≤ b1DoubleLog N → ¬ p ∣ m := by
  classical
  obtain ⟨k, r, q, hk, hr, hq, rfl⟩ := mem_b1Cofactors_iff.mp hm
  have hkgap := (Finset.mem_filter.mp hk).1
  have hgap := (gapSmallFactors_odd_and_no_intermediate_prime hkgap).2
  intro p hp hyp hpZ hpdvd
  have hpN : p ≤ N := hpZ.trans
    ((Nat.log_le_self 2 (Nat.log 2 N)).trans (Nat.log_le_self 2 N))
  have hNpow : N < N ^ 4 := by
    have hN2 : N < N ^ 2 := by nlinarith
    exact hN2.trans_le (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hrp := (mem_middlePrimes_iff.mp hr).2.2
  have hqp := (mem_largePrimes_iff.mp hq).2.2
  have hNr : N < r := hNpow.trans_le (mem_middlePrimes_iff.mp hr).1
  have hNq : N < q := hNpow.trans_le
    ((Nat.pow_le_pow_right (by omega) (by norm_num : 4 ≤ 21)).trans
      (mem_largePrimes_iff.mp hq).1)
  rcases hp.dvd_mul.mp hpdvd with hkr | hqdiv
  · rcases hp.dvd_mul.mp hkr with hkdiv | hrdiv
    · exact hgap p hp hyp hpZ hkdiv
    · have hpr := (Nat.prime_dvd_prime_iff_eq hp hrp).mp hrdiv
      omega
  · have hpq := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hqdiv
    omega

#print axioms exists_eventually_sum_inv_b1Cofactors_lower

end Erdos822
