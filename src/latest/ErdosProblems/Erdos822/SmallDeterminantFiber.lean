/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.StructuredDeterminantResidues
import ErdosProblems.Erdos822.IntegerResidueBlocks
import ErdosProblems.Erdos822.LargeGcdFreeFilter

/-!
# A fixed small-range determinant-prime fiber

Fix the small factor, middle prime, anchor cofactor, common divisor, and a
prime charged by the reduced determinant.  The admissible large primes lie
in one progression modulo the product of the common divisor and determinant
prime.  The elementary arbitrary-modulus block bound then controls their
reciprocal mass.
-/

namespace Erdos822

open scoped BigOperators

/-- Large primes simultaneously supported by a collision, a common shifted
divisor `h`, and a determinant prime `p`. -/
def smallDeterminantLargePrimeFiber
    (N x k r m' p h : ℕ) : Finset ℕ :=
  (largePrimes N).filter fun q =>
    (outerCollisionPairs x (k * r * q) m').Nonempty ∧
      h ∣ shiftedCoefficientGcd (k * r * q) m' ∧
      p ∣ reducedTotientDet (k * r * q) m'

@[simp]
theorem mem_smallDeterminantLargePrimeFiber_iff
    {N x k r m' p h q : ℕ} :
    q ∈ smallDeterminantLargePrimeFiber N x k r m' p h ↔
      q ∈ largePrimes N ∧
        (outerCollisionPairs x (k * r * q) m').Nonempty ∧
        h ∣ shiftedCoefficientGcd (k * r * q) m' ∧
        p ∣ reducedTotientDet (k * r * q) m' := by
  simp [smallDeterminantLargePrimeFiber, and_assoc]

/-- A nonempty fixed fiber is contained in one large-prime residue class
modulo `p*h`. -/
theorem smallDeterminantLargePrimeFiber_subset_mul_residueClass
    {N x k r m' p h y : ℕ}
    (hN : 2 ≤ N) (hp : p.Prime)
    (hk : k ∈ oddSmallFactors N) (hr : r ∈ middlePrimes N)
    (hm' : 0 < m')
    (hlarge : ∀ q ∈ largePrimes N,
      ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hpK : ¬ p ∣ Nat.totient k) (hpR : ¬ p ∣ r - 1)
    (hcoef : Nat.Coprime h (k * r))
    (hph : Nat.Coprime p h) (hy : y < N ^ 21)
    (hne : (smallDeterminantLargePrimeFiber N x k r m' p h).Nonempty) :
    let q₀ := (smallDeterminantLargePrimeFiber N x k r m' p h).min' hne
    smallDeterminantLargePrimeFiber N x k r m' p h ⊆
      largePrimeResidueClass N (p * h) q₀ y := by
  classical
  let Q := smallDeterminantLargePrimeFiber N x k r m' p h
  let q₀ := Q.min' hne
  dsimp only
  have hq₀mem : q₀ ∈ Q := Finset.min'_mem Q hne
  have hq₀data := mem_smallDeterminantLargePrimeFiber_iff.mp hq₀mem
  have hrPrime := (mem_middlePrimes_iff.mp hr).2.2
  have hq₀Prime := (mem_largePrimes_iff.mp hq₀data.1).2.2
  have hq₀sep := (oddCofactorTriples_separated hN (by
    rw [mem_oddCofactorTriples_iff]
    exact ⟨hk, hr, hq₀data.1⟩)).2.2
  have hq₀kr : ¬ q₀ ∣ k * r := by
    intro hd
    have hle := Nat.le_of_dvd
      (Nat.mul_pos (oddSmallFactors_pos hk) hrPrime.pos) hd
    omega
  intro q hq
  have hqdata := mem_smallDeterminantLargePrimeFiber_iff.mp hq
  have hqPrime := (mem_largePrimes_iff.mp hqdata.1).2.2
  have hqsep := (oddCofactorTriples_separated hN (by
    rw [mem_oddCofactorTriples_iff]
    exact ⟨hk, hr, hqdata.1⟩)).2.2
  have hqkr : ¬ q ∣ k * r := by
    intro hd
    have hle := Nat.le_of_dvd
      (Nat.mul_pos (oddSmallFactors_pos hk) hrPrime.pos) hd
    omega
  have hmod : q ≡ q₀ [MOD p * h] :=
    largePrimes_modEq_mul_of_commonDivisor_distance_and_reducedDet
      hp hrPrime hqPrime hq₀Prime
      (by
        intro hd
        have hle := Nat.le_of_dvd (oddSmallFactors_pos hk) hd
        exact (not_lt_of_ge hle)
          (oddCofactorTriples_separated hN (by
            rw [mem_oddCofactorTriples_iff]
            exact ⟨hk, hr, hqdata.1⟩)).2.1)
      hqkr hq₀kr hm'
      (hlarge q hqdata.1) (hlarge q₀ hq₀data.1) hlarge'
      hqdata.2.1 hq₀data.2.1
      hqdata.2.2.1 hq₀data.2.2.1
      hqdata.2.2.2 hq₀data.2.2.2 hpK hpR hcoef hph
  rw [mem_largePrimeResidueClass_iff]
  refine ⟨hqdata.1, ?_, hmod⟩
  have hqLower := (mem_largePrimes_iff.mp hqdata.1).1
  omega

/-- Reciprocal mass of the fixed fiber, with the expected inverse `p*h`
factor and the endpoint error from the elementary block decomposition. -/
theorem sum_inv_smallDeterminantLargePrimeFiber_le
    {N x k r m' p h y : ℕ}
    (hN : 2 ≤ N) (hp : p.Prime)
    (hk : k ∈ oddSmallFactors N) (hr : r ∈ middlePrimes N)
    (hm' : 0 < m')
    (hlarge : ∀ q ∈ largePrimes N,
      ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hpK : ¬ p ∣ Nat.totient k) (hpR : ¬ p ∣ r - 1)
    (hcoef : Nat.Coprime h (k * r))
    (hph : Nat.Coprime p h) (hh : 0 < h) (hy : y < N ^ 21) :
    ∑ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
        (1 : ℝ) / q ≤
      ((1 : ℝ) / (p * h) + (1 : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ) := by
  classical
  by_cases hne :
      (smallDeterminantLargePrimeFiber N x k r m' p h).Nonempty
  · let q₀ := (smallDeterminantLargePrimeFiber N x k r m' p h).min' hne
    have hsub := smallDeterminantLargePrimeFiber_subset_mul_residueClass
      hN hp hk hr hm' hlarge hlarge' hpK hpR hcoef hph hy hne
    calc
      (∑ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
          (1 : ℝ) / q) ≤
          ∑ q ∈ largePrimeResidueClass N (p * h) q₀ y,
            (1 : ℝ) / q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro q hq hnot
        positivity
      _ ≤ ((1 : ℝ) / (p * h) + (1 : ℝ) / (N ^ 21 : ℕ)) *
          (harmonic N : ℝ) := by
        simpa only [Nat.cast_mul] using
          (sum_inv_largePrimeResidueClass_le_harmonic_of_pos
            (a := q₀) (y := y) hN (Nat.mul_pos hp.pos hh))
  · have hempty : smallDeterminantLargePrimeFiber N x k r m' p h = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.sum_empty]
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity

/-- B4-facing form of the fixed-fiber estimate.  Coprimality of `h` with
the fixed factor `k*r` follows from the large-gcd-free condition on any
member of a nonempty fiber, provided every prime factor of `h` is above the
B4 cutoff. -/
theorem sum_inv_smallDeterminantLargePrimeFiber_le_of_largeGcdFree
    {N x k r m' p h cutoff y : ℕ}
    (hN : 2 ≤ N) (hp : p.Prime)
    (hk : k ∈ oddSmallFactors N) (hr : r ∈ middlePrimes N)
    (hm' : 0 < m')
    (hlarge : ∀ q ∈ largePrimes N,
      ∀ s ∈ outerPrimes x (k * r * q), k * r * q < s)
    (hlarge' : ∀ s ∈ outerPrimes x m', m' < s)
    (hpK : ¬ p ∣ Nat.totient k) (hpR : ¬ p ∣ r - 1)
    (hmem : ∀ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
      k * r * q ∈ largeGcdFreeOddCofactors N cutoff)
    (hsupport : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ h → cutoff < ℓ)
    (hph : Nat.Coprime p h) (hh : 0 < h) (hy : y < N ^ 21) :
    ∑ q ∈ smallDeterminantLargePrimeFiber N x k r m' p h,
        (1 : ℝ) / q ≤
      ((1 : ℝ) / (p * h) + (1 : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ) := by
  classical
  by_cases hne :
      (smallDeterminantLargePrimeFiber N x k r m' p h).Nonempty
  · let q₀ := (smallDeterminantLargePrimeFiber N x k r m' p h).min' hne
    have hq₀mem : q₀ ∈ smallDeterminantLargePrimeFiber N x k r m' p h :=
      Finset.min'_mem _ hne
    have hq₀data := mem_smallDeterminantLargePrimeFiber_iff.mp hq₀mem
    have hcoef : Nat.Coprime h (k * r) :=
      commonDivisor_coprime_leftFactor_of_largeGcdFree
        (hmem q₀ hq₀mem) (by exact ⟨q₀, rfl⟩)
        hq₀data.2.2.1 hsupport
    exact sum_inv_smallDeterminantLargePrimeFiber_le
      hN hp hk hr hm' hlarge hlarge' hpK hpR hcoef hph hh hy
  · have hempty : smallDeterminantLargePrimeFiber N x k r m' p h = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.sum_empty]
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity

end Erdos822
