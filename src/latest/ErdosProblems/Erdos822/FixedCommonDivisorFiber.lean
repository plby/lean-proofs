/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.RoughQuadraticPairClasses

/-!
# A fixed common-divisor fiber

Fix the small factor k, an anchor cofactor m', and a divisor h of the
common shifted coefficient.  If the fiber is nonempty, choose one structured
prime pair as a base point.  Every other supported pair then lies in the two
rough quadratic class unions attached to that base point.  This is the
finite covering statement used before summing over h and k.
-/

namespace Erdos822

open scoped BigOperators

/-- Structured prime pairs with fixed small factor which lie in B, support
an outer collision with the anchor, and share the divisor h. -/
def fixedCommonDivisorPrimePairs
    (B : Finset ℕ) (N x k m' h : ℕ) : Finset (ℕ × ℕ) :=
  ((middlePrimes N).product (largePrimes N)).filter fun rq =>
    k * rq.1 * rq.2 ∈ B ∧
      (outerCollisionPairs x (k * rq.1 * rq.2) m').Nonempty ∧
      h ∣ shiftedCoefficientGcd (k * rq.1 * rq.2) m'

@[simp]
theorem mem_fixedCommonDivisorPrimePairs_iff
    {B : Finset ℕ} {N x k m' h r q : ℕ} :
    (r, q) ∈ fixedCommonDivisorPrimePairs B N x k m' h ↔
      r ∈ middlePrimes N ∧ q ∈ largePrimes N ∧
        k * r * q ∈ B ∧
        (outerCollisionPairs x (k * r * q) m').Nonempty ∧
        h ∣ shiftedCoefficientGcd (k * r * q) m' := by
  simp [fixedCommonDivisorPrimePairs, and_assoc]

/-- A nonempty fixed (k,m',h) fiber is covered by one product of rough
quadratic class unions. -/
theorem exists_quadraticClasses_cover_fixedCommonDivisorPrimePairs
    {B : Finset ℕ} {N x y k m' h : ℕ}
    (hN : 2 ≤ N) (hx : x = N ^ 60) (hyN : y < N ^ 21)
    (hk : k ∈ oddSmallFactors N)
    (hB : B ⊆ squarefreeLargeGcdFreeOddCofactors N y)
    (hm'B : m' ∈ B)
    (hne : (fixedCommonDivisorPrimePairs B N x k m' h).Nonempty) :
    ∃ r₀ q₀ : ℕ,
      (r₀, q₀) ∈ fixedCommonDivisorPrimePairs B N x k m' h ∧
      fixedCommonDivisorPrimePairs B N x k m' h ⊆
        (quadraticMiddlePrimeClasses N (roughPart h y)
          (r₀ * q₀) (r₀ + q₀)).product
          (quadraticLargePrimeClasses N (roughPart h y)
            (r₀ * q₀) (r₀ + q₀) y) := by
  classical
  subst x
  obtain ⟨⟨r₀, q₀⟩, hrq₀⟩ := hne
  refine ⟨r₀, q₀, hrq₀, ?_⟩
  intro rq hrq
  rcases rq with ⟨r, q⟩
  have hdata := mem_fixedCommonDivisorPrimePairs_iff.mp hrq
  have hbase := mem_fixedCommonDivisorPrimePairs_iff.mp hrq₀
  have hm : k * r * q ∈ squarefreeLargeGcdFreeOddCofactors N y :=
    hB hdata.2.2.1
  have hm₀ : k * r₀ * q₀ ∈ squarefreeLargeGcdFreeOddCofactors N y :=
    hB hbase.2.2.1
  have hm' : m' ∈ squarefreeLargeGcdFreeOddCofactors N y := hB hm'B
  have hraw : k * r * q ∈ oddRawCofactors N :=
    squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N y hm
  have hraw₀ : k * r₀ * q₀ ∈ oddRawCofactors N :=
    squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N y hm₀
  have hraw' : m' ∈ oddRawCofactors N :=
    squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N y hm'
  have hlarge : ∀ p ∈ outerPrimes (N ^ 60) (k * r * q),
      k * r * q < p := by
    intro p hp
    exact oddOuterPrime_large_of_mem hN hraw hp
  have hlarge₀ : ∀ p ∈ outerPrimes (N ^ 60) (k * r₀ * q₀),
      k * r₀ * q₀ < p := by
    intro p hp
    exact oddOuterPrime_large_of_mem hN hraw₀ hp
  have hlarge' : ∀ p ∈ outerPrimes (N ^ 60) m', m' < p := by
    intro p hp
    exact oddOuterPrime_large_of_mem hN hraw' hp
  have hsep : 0 < k ∧ k < r ∧ k * r < q :=
    oddCofactorTriples_separated hN (by
      rw [mem_oddCofactorTriples_iff]
      exact ⟨hk, hdata.1, hdata.2.1⟩)
  have hsep₀ : 0 < k ∧ k < r₀ ∧ k * r₀ < q₀ :=
    oddCofactorTriples_separated hN (by
      rw [mem_oddCofactorTriples_iff]
      exact ⟨hk, hbase.1, hbase.2.1⟩)
  have hrPrime := (mem_middlePrimes_iff.mp hdata.1).2.2
  have hqPrime := (mem_largePrimes_iff.mp hdata.2.1).2.2
  have hr₀Prime := (mem_middlePrimes_iff.mp hbase.1).2.2
  have hq₀Prime := (mem_largePrimes_iff.mp hbase.2.1).2.2
  have hrk : ¬ r ∣ k := by
    intro hdiv
    have : r ≤ k := Nat.le_of_dvd hsep.1 hdiv
    omega
  have hqkr : ¬ q ∣ k * r := by
    intro hdiv
    have : q ≤ k * r := Nat.le_of_dvd (Nat.mul_pos hsep.1 hrPrime.pos) hdiv
    omega
  have hr₀k : ¬ r₀ ∣ k := by
    intro hdiv
    have : r₀ ≤ k := Nat.le_of_dvd hsep₀.1 hdiv
    omega
  have hq₀kr₀ : ¬ q₀ ∣ k * r₀ := by
    intro hdiv
    have : q₀ ≤ k * r₀ :=
      Nat.le_of_dvd (Nat.mul_pos hsep₀.1 hr₀Prime.pos) hdiv
    omega
  apply Finset.mem_product.mpr
  constructor
  · exact middlePrime_mem_quadraticClasses_of_rough_commonDivisor
      hm hm₀ (oddRawCofactors_pos hraw')
      hlarge hlarge₀ hlarge'
      hdata.2.2.2.1 hbase.2.2.2.1
      hdata.2.2.2.2 hbase.2.2.2.2
      rfl rfl hrPrime hqPrime hr₀Prime hq₀Prime
      hrk hqkr hr₀k hq₀kr₀ hdata.1
  · exact largePrime_mem_quadraticClasses_of_rough_commonDivisor
      hyN hm hm₀ (oddRawCofactors_pos hraw')
      hlarge hlarge₀ hlarge'
      hdata.2.2.2.1 hbase.2.2.2.1
      hdata.2.2.2.2 hbase.2.2.2.2
      rfl rfl hrPrime hqPrime hr₀Prime hq₀Prime
      hrk hqkr hr₀k hq₀kr₀ hdata.2.1

/-- The reciprocal (r,q) mass in a fixed supported common-divisor fiber
is bounded by the two rough quadratic class estimates. -/
theorem sum_inv_fixedCommonDivisorPrimePairs_le_rough_classes
    {B : Finset ℕ} {N x y k m' h : ℕ}
    (hN : 2 ≤ N) (hx : x = N ^ 60) (hyN : y < N ^ 21)
    (hk : k ∈ oddSmallFactors N)
    (hB : B ⊆ squarefreeLargeGcdFreeOddCofactors N y)
    (hm'B : m' ∈ B) :
    ∑ rq ∈ fixedCommonDivisorPrimePairs B N x k m' h,
        (1 : ℝ) / (rq.1 * rq.2) ≤
      ((2 ^ (roughPart h y).primeFactors.card : ℕ) : ℝ) ^ 2 *
        ((((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 4 : ℕ)) *
            (harmonic N : ℝ)) *
          (((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 21 : ℕ)) *
            (harmonic N : ℝ))) := by
  classical
  by_cases hne : (fixedCommonDivisorPrimePairs B N x k m' h).Nonempty
  · obtain ⟨r₀, q₀, hbase, hsub⟩ :=
      exists_quadraticClasses_cover_fixedCommonDivisorPrimePairs
        hN hx hyN hk hB hm'B hne
    have hsum :
        ∑ rq ∈ fixedCommonDivisorPrimePairs B N x k m' h,
            (1 : ℝ) / (rq.1 * rq.2) ≤
          ∑ r ∈ quadraticMiddlePrimeClasses N (roughPart h y)
              (r₀ * q₀) (r₀ + q₀),
            ∑ q ∈ quadraticLargePrimeClasses N (roughPart h y)
              (r₀ * q₀) (r₀ + q₀) y,
              (1 : ℝ) / (r * q) := by
      calc
        (∑ rq ∈ fixedCommonDivisorPrimePairs B N x k m' h,
            (1 : ℝ) / (rq.1 * rq.2)) ≤
            ∑ rq ∈
              (quadraticMiddlePrimeClasses N (roughPart h y)
                (r₀ * q₀) (r₀ + q₀)).product
                (quadraticLargePrimeClasses N (roughPart h y)
                  (r₀ * q₀) (r₀ + q₀) y),
              (1 : ℝ) / (rq.1 * rq.2) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro rq hrq hnot
          positivity
        _ = ∑ r ∈ quadraticMiddlePrimeClasses N (roughPart h y)
              (r₀ * q₀) (r₀ + q₀),
            ∑ q ∈ quadraticLargePrimeClasses N (roughPart h y)
              (r₀ * q₀) (r₀ + q₀) y,
              (1 : ℝ) / (r * q) := by
          change
            (∑ rq ∈
                (quadraticMiddlePrimeClasses N (roughPart h y)
                  (r₀ * q₀) (r₀ + q₀)) ×ˢ
                (quadraticLargePrimeClasses N (roughPart h y)
                  (r₀ * q₀) (r₀ + q₀) y),
              (1 : ℝ) / (rq.1 * rq.2)) = _
          rw [Finset.sum_product]
    exact hsum.trans
      (sum_inv_quadraticPairClasses_roughPart_le_two_pow_sq
        (N := N) (y := y) (h := h)
        (m := k * r₀ * q₀) (m' := m')
        (u := r₀ * q₀) (v := r₀ + q₀)
        hN (hB (mem_fixedCommonDivisorPrimePairs_iff.mp hbase).2.2.1)
        (mem_fixedCommonDivisorPrimePairs_iff.mp hbase).2.2.2.2)
  · have hempty : fixedCommonDivisorPrimePairs B N x k m' h = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.sum_empty]
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity

/-- Restoring the fixed small-factor denominator simply multiplies the
fixed-fiber estimate by `1/k`. -/
theorem sum_inv_cofactor_fixedCommonDivisorPrimePairs_le_rough_classes
    {B : Finset ℕ} {N x y k m' h : ℕ}
    (hN : 2 ≤ N) (hx : x = N ^ 60) (hyN : y < N ^ 21)
    (hk : k ∈ oddSmallFactors N)
    (hB : B ⊆ squarefreeLargeGcdFreeOddCofactors N y)
    (hm'B : m' ∈ B) :
    ∑ rq ∈ fixedCommonDivisorPrimePairs B N x k m' h,
        (1 : ℝ) / (k * rq.1 * rq.2) ≤
      ((1 : ℝ) / k) *
        (((2 ^ (roughPart h y).primeFactors.card : ℕ) : ℝ) ^ 2 *
          ((((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 4 : ℕ)) *
              (harmonic N : ℝ)) *
            (((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 21 : ℕ)) *
              (harmonic N : ℝ)))) := by
  have hbase := sum_inv_fixedCommonDivisorPrimePairs_le_rough_classes
    (h := h) hN hx hyN hk hB hm'B
  calc
    (∑ rq ∈ fixedCommonDivisorPrimePairs B N x k m' h,
        (1 : ℝ) / (k * rq.1 * rq.2)) =
        ((1 : ℝ) / k) *
          ∑ rq ∈ fixedCommonDivisorPrimePairs B N x k m' h,
            (1 : ℝ) / (rq.1 * rq.2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rq hrq
      push_cast
      ring
    _ ≤ ((1 : ℝ) / k) *
        (((2 ^ (roughPart h y).primeFactors.card : ℕ) : ℝ) ^ 2 *
          ((((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 4 : ℕ)) *
              (harmonic N : ℝ)) *
            (((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 21 : ℕ)) *
              (harmonic N : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left hbase (by positivity)

/-- Named arithmetic factor remaining after the fixed `(k,m',h)` fiber is
covered by the two rough quadratic class unions. -/
noncomputable def roughQuadraticPairMassBound (N y h : ℕ) : ℝ :=
  ((2 ^ (roughPart h y).primeFactors.card : ℕ) : ℝ) ^ 2 *
    ((((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 4 : ℕ)) *
        (harmonic N : ℝ)) *
      (((1 : ℝ) / roughPart h y + (1 : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ)))

theorem roughQuadraticPairMassBound_nonneg (N y h : ℕ) :
    0 ≤ roughQuadraticPairMassBound N y h := by
  unfold roughQuadraticPairMassBound
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  positivity

/-- Summing the fixed-divisor fiber bound over all small factors restores
only the ordinary odd harmonic mass. -/
theorem sum_inv_fixedCommonDivisorPrimePairs_over_k_le
    {B : Finset ℕ} {N x y m' h : ℕ}
    (hN : 2 ≤ N) (hx : x = N ^ 60) (hyN : y < N ^ 21)
    (hB : B ⊆ squarefreeLargeGcdFreeOddCofactors N y)
    (hm'B : m' ∈ B) :
    ∑ k ∈ oddSmallFactors N,
      ∑ rq ∈ fixedCommonDivisorPrimePairs B N x k m' h,
        (1 : ℝ) / (k * rq.1 * rq.2) ≤
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        roughQuadraticPairMassBound N y h := by
  calc
    (∑ k ∈ oddSmallFactors N,
        ∑ rq ∈ fixedCommonDivisorPrimePairs B N x k m' h,
          (1 : ℝ) / (k * rq.1 * rq.2)) ≤
        ∑ k ∈ oddSmallFactors N,
          ((1 : ℝ) / k) * roughQuadraticPairMassBound N y h := by
      apply Finset.sum_le_sum
      intro k hk
      simpa [roughQuadraticPairMassBound] using
        sum_inv_cofactor_fixedCommonDivisorPrimePairs_le_rough_classes
          (B := B) (N := N) (x := x) (y := y)
          (k := k) (m' := m') (h := h)
          hN hx hyN hk hB hm'B
    _ = (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        roughQuadraticPairMassBound N y h := by
      rw [Finset.sum_mul]

end Erdos822
