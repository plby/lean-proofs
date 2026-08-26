/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SmallDeterminantFiber
import ErdosProblems.Erdos822.ReciprocalSquareTail

/-!
# Averaging the small-range determinant-prime fibers

The large prime occurring in the outer cofactor carries reciprocal weight.
After charging a determinant prime `p`, that weight supplies one more factor
`1/p` beyond the progression modulus bound `1/(p*h)`.  Thus the main term is
controlled by a reciprocal-square tail rather than a divergent reciprocal
prime sum.
-/

namespace Erdos822

open scoped BigOperators

/-- Admissible determinant primes in a finite interval.  The exclusions are
exactly those required by the determinant-residue lemma. -/
def smallDeterminantPrimes
    (U z k r h : ℕ) : Finset ℕ :=
  (Finset.Ioc z U).filter fun p =>
    p.Prime ∧ ¬p ∣ Nat.totient k ∧ ¬p ∣ r - 1 ∧ Nat.Coprime p h

@[simp]
theorem mem_smallDeterminantPrimes_iff
    {U z k r h p : ℕ} :
    p ∈ smallDeterminantPrimes U z k r h ↔
      z < p ∧ p ≤ U ∧ p.Prime ∧ ¬p ∣ Nat.totient k ∧
        ¬p ∣ r - 1 ∧ Nat.Coprime p h := by
  simp [smallDeterminantPrimes, and_assoc]

/-- The reciprocal-square mass of admissible determinant primes has the
uniform tail bound `1/z`. -/
theorem sum_inv_sq_smallDeterminantPrimes_le
    {U z k r h : ℕ} (hz : 1 ≤ z) :
    ∑ p ∈ smallDeterminantPrimes U z k r h,
        (1 : ℝ) / (p ^ 2 : ℕ) ≤ (1 : ℝ) / z := by
  apply sum_inv_sq_le_inv_of_subset_Ioc (U := U) hz
  intro p hp
  exact Finset.mem_Ioc.mpr
    ⟨(mem_smallDeterminantPrimes_iff.mp hp).1,
      (mem_smallDeterminantPrimes_iff.mp hp).2.1⟩

/-- The ordinary reciprocal mass is bounded by cardinality times the
reciprocal cutoff.  It is used only for the `N⁻²¹` endpoint error. -/
theorem sum_inv_smallDeterminantPrimes_le_card_div
    {U z k r h : ℕ} (hz : 1 ≤ z) :
    ∑ p ∈ smallDeterminantPrimes U z k r h, (1 : ℝ) / p ≤
      ((smallDeterminantPrimes U z k r h).card : ℝ) / z := by
  calc
    (∑ p ∈ smallDeterminantPrimes U z k r h, (1 : ℝ) / p) ≤
        ∑ _p ∈ smallDeterminantPrimes U z k r h, (1 : ℝ) / z := by
      apply Finset.sum_le_sum
      intro p hp
      have hzp : z ≤ p :=
        (mem_smallDeterminantPrimes_iff.mp hp).1.le
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hzp)
    _ = ((smallDeterminantPrimes U z k r h).card : ℝ) / z := by
      rw [Finset.sum_const]
      simp
      ring

theorem card_smallDeterminantPrimes_le
    (U z k r h : ℕ) :
    (smallDeterminantPrimes U z k r h).card ≤ U := by
  calc
    (smallDeterminantPrimes U z k r h).card ≤
        (Finset.Ioc z U).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ U := by simp

/-- Averaging fixed determinant-prime fibers produces a reciprocal-square
main term.  The second term is the harmless endpoint error of the elementary
residue-block decomposition. -/
theorem sum_weighted_smallDeterminantLargePrimeFiber_le
    {N x k r m' h U z y : ℕ}
    (hN : 2 ≤ N) (hk : k ∈ oddSmallFactors N)
    (hr : r ∈ middlePrimes N) (hm' : 0 < m')
    (hlarge : ∀ q ∈ largePrimes N,
      ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hcoef : Nat.Coprime h (k * r))
    (hh : 0 < h) (hy : y < N ^ 21) :
    ∑ p ∈ smallDeterminantPrimes U z k r h,
        ((1 : ℝ) / p) *
          (∑ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
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
          (∑ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
            (1 : ℝ) / q)) ≤
        ∑ p ∈ smallDeterminantPrimes U z k r h,
          ((1 : ℝ) / p) *
            (((1 : ℝ) / (p * h) + (1 : ℝ) / (N ^ 21 : ℕ)) *
              (harmonic N : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := mem_smallDeterminantPrimes_iff.mp hp
      exact mul_le_mul_of_nonneg_left
        (sum_inv_smallDeterminantLargePrimeFiber_le
          hN hpData.2.2.1 hk hr hm' hlarge hlarge'
          hpData.2.2.2.1 hpData.2.2.2.2.1 hcoef
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
        Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      have hpPrime := (mem_smallDeterminantPrimes_iff.mp hp).2.2.1
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
      have hh0 : (h : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
      push_cast
      field_simp

/-- B4-facing averaged form.  It derives the single cofactor-coprimality
hypothesis needed by the preceding theorem from any nonempty charged fiber;
if all charged fibers are empty, the estimate is immediate. -/
theorem sum_weighted_smallDeterminantLargePrimeFiber_le_of_largeGcdFree
    {N x k r m' h U z cutoff y : ℕ}
    (hN : 2 ≤ N) (hk : k ∈ oddSmallFactors N)
    (hr : r ∈ middlePrimes N) (hm' : 0 < m')
    (hlarge : ∀ q ∈ largePrimes N,
      ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hmem : ∀ p ∈ smallDeterminantPrimes U z k r h,
      ∀ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
        k * r * q ∈ largeGcdFreeOddCofactors N cutoff)
    (hsupport : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → cutoff < ℓ)
    (hh : 0 < h) (hy : y < N ^ 21) :
    ∑ p ∈ smallDeterminantPrimes U z k r h,
        ((1 : ℝ) / p) *
          (∑ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
            (1 : ℝ) / q) ≤
      (harmonic N : ℝ) *
        (((1 : ℝ) / h) *
            (∑ p ∈ smallDeterminantPrimes U z k r h,
              (1 : ℝ) / (p ^ 2 : ℕ)) +
          ((1 : ℝ) / (N ^ 21 : ℕ)) *
            (∑ p ∈ smallDeterminantPrimes U z k r h,
              (1 : ℝ) / p)) := by
  classical
  by_cases hsome : ∃ p ∈ smallDeterminantPrimes U z k r h,
      (smallDeterminantLargePrimeFiber N x k r m' p h).Nonempty
  · obtain ⟨p, hp, q, hq⟩ := hsome
    have hqData := mem_smallDeterminantLargePrimeFiber_iff.mp hq
    have hcoef : Nat.Coprime h (k * r) :=
      commonDivisor_coprime_leftFactor_of_largeGcdFree
        (hmem p hp q hq) (by exact ⟨q, rfl⟩)
        hqData.2.2.1 hsupport
    exact sum_weighted_smallDeterminantLargePrimeFiber_le
      (U := U) (z := z) hN hk hr hm' hlarge hlarge' hcoef hh hy
  · have hempty : ∀ p ∈ smallDeterminantPrimes U z k r h,
        smallDeterminantLargePrimeFiber N x k r m' p h = ∅ := by
      intro p hp
      exact Finset.not_nonempty_iff_eq_empty.mp (by
        intro hne
        exact hsome ⟨p, hp, hne⟩)
    have hleft :
        (∑ p ∈ smallDeterminantPrimes U z k r h,
          ((1 : ℝ) / p) *
            (∑ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
              (1 : ℝ) / q)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [hempty p hp]
      simp
    rw [hleft]
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity

/-- Cutoff form of the weighted determinant-prime average.  The main term
is `1/(h*z)`; only the elementary block endpoint error retains the finite
number of charged primes. -/
theorem sum_weighted_smallDeterminantLargePrimeFiber_le_cutoff
    {N x k r m' h U z y : ℕ}
    (hN : 2 ≤ N) (hk : k ∈ oddSmallFactors N)
    (hr : r ∈ middlePrimes N) (hm' : 0 < m')
    (hlarge : ∀ q ∈ largePrimes N,
      ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hcoef : Nat.Coprime h (k * r))
    (hh : 0 < h) (hz : 1 ≤ z) (hy : y < N ^ 21) :
    ∑ p ∈ smallDeterminantPrimes U z k r h,
        ((1 : ℝ) / p) *
          (∑ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
            (1 : ℝ) / q) ≤
      (harmonic N : ℝ) *
        (((1 : ℝ) / h) * ((1 : ℝ) / z) +
          ((1 : ℝ) / (N ^ 21 : ℕ)) *
            (((smallDeterminantPrimes U z k r h).card : ℝ) / z)) := by
  have havg := sum_weighted_smallDeterminantLargePrimeFiber_le
    (U := U) (z := z)
    hN hk hr hm' hlarge hlarge' hcoef hh hy
  refine havg.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity)
  gcongr
  · exact sum_inv_sq_smallDeterminantPrimes_le hz
  · exact sum_inv_smallDeterminantPrimes_le_card_div hz

/-- B4-facing cutoff form of the determinant-prime average. -/
theorem sum_weighted_smallDeterminantLargePrimeFiber_le_cutoff_of_largeGcdFree
    {N x k r m' h U z cutoff y : ℕ}
    (hN : 2 ≤ N) (hk : k ∈ oddSmallFactors N)
    (hr : r ∈ middlePrimes N) (hm' : 0 < m')
    (hlarge : ∀ q ∈ largePrimes N,
      ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hmem : ∀ p ∈ smallDeterminantPrimes U z k r h,
      ∀ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
        k * r * q ∈ largeGcdFreeOddCofactors N cutoff)
    (hsupport : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → cutoff < ℓ)
    (hh : 0 < h) (hz : 1 ≤ z) (hy : y < N ^ 21) :
    ∑ p ∈ smallDeterminantPrimes U z k r h,
        ((1 : ℝ) / p) *
          (∑ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
            (1 : ℝ) / q) ≤
      (harmonic N : ℝ) *
        (((1 : ℝ) / h) * ((1 : ℝ) / z) +
          ((1 : ℝ) / (N ^ 21 : ℕ)) *
            (((smallDeterminantPrimes U z k r h).card : ℝ) / z)) := by
  have havg :=
    sum_weighted_smallDeterminantLargePrimeFiber_le_of_largeGcdFree
      (U := U) (z := z) (cutoff := cutoff)
      hN hk hr hm' hlarge hlarge' hmem hsupport hh hy
  refine havg.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity)
  gcongr
  · exact sum_inv_sq_smallDeterminantPrimes_le hz
  · exact sum_inv_smallDeterminantPrimes_le_card_div hz

/-- Fully numerical endpoint form: the number of charged primes is at most
the upper endpoint `U`. -/
theorem sum_weighted_smallDeterminantLargePrimeFiber_le_cutoff_card
    {N x k r m' h U z cutoff y : ℕ}
    (hN : 2 ≤ N) (hk : k ∈ oddSmallFactors N)
    (hr : r ∈ middlePrimes N) (hm' : 0 < m')
    (hlarge : ∀ q ∈ largePrimes N,
      ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hmem : ∀ p ∈ smallDeterminantPrimes U z k r h,
      ∀ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
        k * r * q ∈ largeGcdFreeOddCofactors N cutoff)
    (hsupport : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → cutoff < ℓ)
    (hh : 0 < h) (hz : 1 ≤ z) (hy : y < N ^ 21) :
    ∑ p ∈ smallDeterminantPrimes U z k r h,
        ((1 : ℝ) / p) *
          (∑ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
            (1 : ℝ) / q) ≤
      (harmonic N : ℝ) *
        (((1 : ℝ) / h) * ((1 : ℝ) / z) +
          ((1 : ℝ) / (N ^ 21 : ℕ)) * ((U : ℝ) / z)) := by
  refine (sum_weighted_smallDeterminantLargePrimeFiber_le_cutoff_of_largeGcdFree
    hN hk hr hm' hlarge hlarge' hmem hsupport hh hz hy).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity)
  gcongr
  exact_mod_cast card_smallDeterminantPrimes_le U z k r h

end Erdos822
