/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SmallDeterminantPrimeAverage

/-!
# Determinant-prime fibers inside a filtered B4 family

The global energy sum ranges over a selected cofactor family `B`.  Keeping
that membership in the fiber is essential: a base point chosen from a
nonempty fiber then inherits the B4 large-gcd-free condition.
-/

namespace Erdos822

open scoped BigOperators

def smallDeterminantLargePrimeFiberIn
    (B : Finset ℕ) (N x k r m' p h : ℕ) : Finset ℕ :=
  (smallDeterminantLargePrimeFiber N x k r m' p h).filter fun q =>
    k * r * q ∈ B

@[simp]
theorem mem_smallDeterminantLargePrimeFiberIn_iff
    {B : Finset ℕ} {N x k r m' p h q : ℕ} :
    q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h ↔
      q ∈ smallDeterminantLargePrimeFiber N x k r m' p h ∧
        k * r * q ∈ B := by
  simp [smallDeterminantLargePrimeFiberIn]

theorem smallDeterminantLargePrimeFiberIn_subset
    (B : Finset ℕ) (N x k r m' p h : ℕ) :
    smallDeterminantLargePrimeFiberIn B N x k r m' p h ⊆
      smallDeterminantLargePrimeFiber N x k r m' p h :=
  Finset.filter_subset _ _

/-- Fixed-prime reciprocal bound inside a B4-filtered family. -/
theorem sum_inv_smallDeterminantLargePrimeFiberIn_le
    {B : Finset ℕ} {N x k r m' p h cutoff y : ℕ}
    (hN : 2 ≤ N) (hp : p.Prime)
    (hk : k ∈ oddSmallFactors N) (hr : r ∈ middlePrimes N)
    (hm' : 0 < m')
    (hlarge : ∀ q ∈ largePrimes N,
      ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hpK : ¬ p ∣ Nat.totient k) (hpR : ¬ p ∣ r - 1)
    (hB : B ⊆ largeGcdFreeOddCofactors N cutoff)
    (hsupport : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → cutoff < ℓ)
    (hph : Nat.Coprime p h) (hh : 0 < h) (hy : y < N ^ 21) :
    ∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h,
        (1 : ℝ) / q ≤
      ((1 : ℝ) / (p * h) + (1 : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ) := by
  classical
  by_cases hne :
      (smallDeterminantLargePrimeFiberIn B N x k r m' p h).Nonempty
  · let q₀ := (smallDeterminantLargePrimeFiberIn B N x k r m' p h).min' hne
    have hq₀mem : q₀ ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h :=
      Finset.min'_mem _ hne
    have hq₀data := mem_smallDeterminantLargePrimeFiberIn_iff.mp hq₀mem
    have hbaseData := mem_smallDeterminantLargePrimeFiber_iff.mp hq₀data.1
    have hcoef : Nat.Coprime h (k * r) :=
      commonDivisor_coprime_leftFactor_of_largeGcdFree
        (hB hq₀data.2) (by exact ⟨q₀, rfl⟩)
        hbaseData.2.2.1 hsupport
    calc
      (∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h,
          (1 : ℝ) / q) ≤
          ∑ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
            (1 : ℝ) / q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (smallDeterminantLargePrimeFiberIn_subset B N x k r m' p h)
        intro q hq hnot
        positivity
      _ ≤ ((1 : ℝ) / (p * h) + (1 : ℝ) / (N ^ 21 : ℕ)) *
          (harmonic N : ℝ) :=
        sum_inv_smallDeterminantLargePrimeFiber_le
          hN hp hk hr hm' hlarge hlarge' hpK hpR hcoef hph hh hy
  · have hempty : smallDeterminantLargePrimeFiberIn B N x k r m' p h = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.sum_empty]
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity

/-- The filtered determinant-prime average. -/
theorem sum_weighted_smallDeterminantLargePrimeFiberIn_le
    {B : Finset ℕ} {N x k r m' h U z cutoff y : ℕ}
    (hN : 2 ≤ N) (hk : k ∈ oddSmallFactors N)
    (hr : r ∈ middlePrimes N) (hm' : 0 < m')
    (hlarge : ∀ q ∈ largePrimes N,
      ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hB : B ⊆ largeGcdFreeOddCofactors N cutoff)
    (hsupport : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → cutoff < ℓ)
    (hh : 0 < h) (hy : y < N ^ 21) :
    ∑ p ∈ smallDeterminantPrimes U z k r h,
        ((1 : ℝ) / p) *
          (∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h,
            (1 : ℝ) / q) ≤
      (harmonic N : ℝ) *
        (((1 : ℝ) / h) *
            (∑ p ∈ smallDeterminantPrimes U z k r h,
              (1 : ℝ) / (p ^ 2 : ℕ)) +
          ((1 : ℝ) / (N ^ 21 : ℕ)) *
            (∑ p ∈ smallDeterminantPrimes U z k r h,
              (1 : ℝ) / p)) := by
  classical
  calc
    (∑ p ∈ smallDeterminantPrimes U z k r h,
        ((1 : ℝ) / p) *
          (∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h,
            (1 : ℝ) / q)) ≤
        ∑ p ∈ smallDeterminantPrimes U z k r h,
          ((1 : ℝ) / p) *
            (((1 : ℝ) / (p * h) + (1 : ℝ) / (N ^ 21 : ℕ)) *
              (harmonic N : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := mem_smallDeterminantPrimes_iff.mp hp
      exact mul_le_mul_of_nonneg_left
        (sum_inv_smallDeterminantLargePrimeFiberIn_le
          hN hpData.2.2.1 hk hr hm' hlarge hlarge'
          hpData.2.2.2.1 hpData.2.2.2.2.1 hB hsupport
          hpData.2.2.2.2.2 hh hy)
        (by positivity)
    _ = (harmonic N : ℝ) *
        (((1 : ℝ) / h) *
            (∑ p ∈ smallDeterminantPrimes U z k r h,
              (1 : ℝ) / (p ^ 2 : ℕ)) +
          ((1 : ℝ) / (N ^ 21 : ℕ)) *
            (∑ p ∈ smallDeterminantPrimes U z k r h,
              (1 : ℝ) / p)) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hpPrime := (mem_smallDeterminantPrimes_iff.mp hp).2.2.1
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
      have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
      push_cast
      field_simp

/-- Numerical cutoff form of the filtered determinant-prime average. -/
theorem sum_weighted_smallDeterminantLargePrimeFiberIn_le_cutoff
    {B : Finset ℕ} {N x k r m' h U z cutoff y : ℕ}
    (hN : 2 ≤ N) (hk : k ∈ oddSmallFactors N)
    (hr : r ∈ middlePrimes N) (hm' : 0 < m')
    (hlarge : ∀ q ∈ largePrimes N,
      ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hB : B ⊆ largeGcdFreeOddCofactors N cutoff)
    (hsupport : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → cutoff < ℓ)
    (hh : 0 < h) (hz : 1 ≤ z) (hy : y < N ^ 21) :
    ∑ p ∈ smallDeterminantPrimes U z k r h,
        ((1 : ℝ) / p) *
          (∑ q ∈ smallDeterminantLargePrimeFiberIn B N x k r m' p h,
            (1 : ℝ) / q) ≤
      (harmonic N : ℝ) *
        (((1 : ℝ) / h) * ((1 : ℝ) / z) +
          ((1 : ℝ) / (N ^ 21 : ℕ)) * ((U : ℝ) / z)) := by
  refine (sum_weighted_smallDeterminantLargePrimeFiberIn_le
    hN hk hr hm' hlarge hlarge' hB hsupport hh hy).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity)
  gcongr
  · exact sum_inv_sq_smallDeterminantPrimes_le hz
  · calc
      (∑ p ∈ smallDeterminantPrimes U z k r h, (1 : ℝ) / p) ≤
          ((smallDeterminantPrimes U z k r h).card : ℝ) / z :=
        sum_inv_smallDeterminantPrimes_le_card_div hz
      _ ≤ (U : ℝ) / z := by
        gcongr
        exact_mod_cast card_smallDeterminantPrimes_le U z k r h

end Erdos822
