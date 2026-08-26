/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.FixedCommonDivisorFiber

/-!
# Reassembling fixed common-divisor fibers around one anchor

For an anchor cofactor m' and a fixed divisor h, the structured triple
parameterization identifies the reciprocal mass of all supported cofactors
sharing h with the sum of the fixed `(k,m',h)` prime-pair fibers.  The
previous file then bounds that sum uniformly.
-/

namespace Erdos822

open scoped BigOperators

/-- Exact Fubini identity from supported cofactors with fixed h to the
fixed-small-factor prime-pair fibers. -/
theorem sum_inv_supported_commonDivisor_eq_fixedPrimePairs
    {B : Finset ℕ} {N x m' h : ℕ}
    (hN : 2 ≤ N) (hB : B ⊆ oddRawCofactors N) :
    (∑ m ∈ B,
        if (outerCollisionPairs x m m').Nonempty ∧
            h ∣ shiftedCoefficientGcd m m' then
          (1 : ℝ) / m
        else 0) =
      ∑ k ∈ oddSmallFactors N,
        ∑ rq ∈ fixedCommonDivisorPrimePairs B N x k m' h,
          (1 : ℝ) / (k * rq.1 * rq.2) := by
  rw [sum_subset_oddRawCofactors_eq_triple_if hN hB]
  apply Finset.sum_congr rfl
  intro k hk
  unfold fixedCommonDivisorPrimePairs
  rw [Finset.sum_filter, ← Finset.sum_product']
  apply Finset.sum_congr rfl
  rintro ⟨r, q⟩ hrq
  simp only [and_assoc]
  by_cases hmB : k * r * q ∈ B
  · by_cases hcond :
        (outerCollisionPairs x (k * r * q) m').Nonempty ∧
          h ∣ shiftedCoefficientGcd (k * r * q) m'
    · simp [hmB, hcond]
    · simp [hmB, hcond]
  · simp [hmB]

/-- The fixed-h reciprocal mass around an anchor is bounded by the odd
small-factor harmonic mass times the rough quadratic pair factor. -/
theorem sum_inv_supported_commonDivisor_le_roughPairMass
    {B : Finset ℕ} {N x y m' h : ℕ}
    (hN : 2 ≤ N) (hx : x = N ^ 60) (hyN : y < N ^ 21)
    (hB : B ⊆ squarefreeLargeGcdFreeOddCofactors N y)
    (hm'B : m' ∈ B) :
    (∑ m ∈ B,
        if (outerCollisionPairs x m m').Nonempty ∧
            h ∣ shiftedCoefficientGcd m m' then
          (1 : ℝ) / m
        else 0) ≤
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        roughQuadraticPairMassBound N y h := by
  rw [sum_inv_supported_commonDivisor_eq_fixedPrimePairs hN
    (Set.Subset.trans hB
      (squarefreeLargeGcdFreeOddCofactors_subset_oddRaw N y))]
  exact sum_inv_fixedCommonDivisorPrimePairs_over_k_le
    hN hx hyN hB hm'B

end Erdos822
