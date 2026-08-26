/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.OddCofactorLayers

/-! # Structured cofactors from any restricted small-factor family -/

namespace Erdos822

open Filter
open scoped BigOperators

def restrictedCofactors (N : ℕ) (K : Finset ℕ) : Finset ℕ :=
  (K ×ˢ ((middlePrimes N) ×ˢ (largePrimes N))).image cofactorProduct

theorem restrictedCofactors_subset_oddRaw {N : ℕ} {K : Finset ℕ}
    (hK : K ⊆ oddSmallFactors N) : restrictedCofactors N K ⊆ oddRawCofactors N := by
  apply Finset.image_subset_image
  intro t ht
  obtain ⟨hk, hrq⟩ := Finset.mem_product.mp ht
  exact Finset.mem_product.mpr ⟨hK hk, hrq⟩

theorem mem_restrictedCofactors_iff {N m : ℕ} {K : Finset ℕ} :
    m ∈ restrictedCofactors N K ↔ ∃ k r q : ℕ,
      k ∈ K ∧ r ∈ middlePrimes N ∧ q ∈ largePrimes N ∧ m = k * r * q := by
  simp only [restrictedCofactors, Finset.mem_image, Prod.exists, Finset.mem_product,
    cofactorProduct]
  constructor
  · rintro ⟨k, r, q, ⟨hk, hr, hq⟩, hm⟩
    exact ⟨k, r, q, hk, hr, hq, hm.symm⟩
  · rintro ⟨k, r, q, hk, hr, hq, hm⟩
    exact ⟨k, r, q, ⟨hk, hr, hq⟩, hm.symm⟩

theorem sum_inv_restrictedCofactors_eq_product {N : ℕ} {K : Finset ℕ}
    (hN : 2 ≤ N) (hK : K ⊆ oddSmallFactors N) :
    (∑ m ∈ restrictedCofactors N K, (1 : ℝ) / m) =
      (∑ k ∈ K, (1 : ℝ) / k) * reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) *
        reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) := by
  have hsub : K ×ˢ ((middlePrimes N) ×ˢ (largePrimes N)) ⊆ oddCofactorTriples N := by
    intro t ht
    obtain ⟨hk, hrq⟩ := Finset.mem_product.mp ht
    exact Finset.mem_product.mpr ⟨hK hk, hrq⟩
  rw [restrictedCofactors, Finset.sum_image
    ((cofactorProduct_injOn_oddCofactorTriples hN).mono hsub), Finset.sum_product]
  simp_rw [Finset.sum_product]
  rw [middlePrimes_eq_primesLE_sdiff, largePrimes_eq_primesLE_sdiff]
  simp only [reciprocalPrimeIntervalSum, cofactorProduct, Nat.cast_mul, one_div, mul_inv]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]

theorem eventually_sum_inv_restrictedCofactors_lower
    {K : ℕ → Finset ℕ} {c : ℝ} (_hc : 0 < c)
    (hK : ∀ N, K N ⊆ oddSmallFactors N)
    (hmass : ∀ᶠ N : ℕ in atTop, c * Real.log (N : ℝ) ≤ ∑ k ∈ K N, (1 : ℝ) / k) :
    ∀ᶠ N : ℕ in atTop,
      c / 500 * Real.log (N : ℝ) ≤ ∑ m ∈ restrictedCofactors N (K N), (1 : ℝ) / m := by
  filter_upwards [hmass, eventually_reciprocalPrimeIntervalSum_four_five_lower,
      eventually_reciprocalPrimeIntervalSum_twentyone_twentytwo_lower,
      eventually_ge_atTop 2] with N hmassN hr hq hN
  have hK0 : 0 ≤ ∑ k ∈ K N, (1 : ℝ) / k := Finset.sum_nonneg fun k hk ↦ by positivity
  have hr0 : 0 ≤ reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) :=
    (by norm_num : (0 : ℝ) ≤ 1 / 10).trans hr
  rw [sum_inv_restrictedCofactors_eq_product hN (hK N)]
  calc
    c / 500 * Real.log (N : ℝ) =
        (c * Real.log (N : ℝ)) * (1 / 10 : ℝ) * (1 / 50 : ℝ) := by ring
    _ ≤ (∑ k ∈ K N, (1 : ℝ) / k) * (1 / 10 : ℝ) * (1 / 50 : ℝ) := by gcongr
    _ ≤ (∑ k ∈ K N, (1 : ℝ) / k) * reciprocalPrimeIntervalSum (N ^ 4) (N ^ 5) *
        reciprocalPrimeIntervalSum (N ^ 21) (N ^ 22) := by gcongr

end Erdos822
