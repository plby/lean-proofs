/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CombinatorialInt

namespace Erdos232

/-- The finite Boolean probability space used by the 23-point certificate. -/
abbrev AtomIndex := Fin (2 ^ 23)

def bitZeroIndicator (s : AtomIndex) : ℝ :=
  if s.val.testBit 0 then 1 else 0

/-- Exact pair contribution, with the common denominator `10^9` still cleared. -/
def pairContributionReal (s : AtomIndex) : ℝ :=
  (atomPairContributionInt s.val : ℝ)

/-- Exact congruence contribution, with the common denominator `10^9` still cleared. -/
def congruenceContributionReal (s : AtomIndex) : ℝ :=
  (atomCongruenceContributionInt s.val : ℝ)

/-- Abstract finite weak duality for the exact integer certificate.

The three displayed expectation identities are precisely the total-mass, distinguished-vertex,
pair-correlation, and congruence rows of the primal linear program.  Keeping them abstract here
separates the exact 13,552-atom computation from the measure-theoretic construction of the atoms. -/
theorem finiteCertificate_bound
    (a : AtomIndex → ℝ) (δ pairValue : ℝ)
    (ha : ∀ s, 0 ≤ a s)
    (hsupport : ∀ s, a s ≠ 0 → 0 ≤ certificateAtomInt s.val)
    (htotal : ∑ s, a s = 1)
    (hvertex : ∑ s, a s * bitZeroIndicator s = δ)
    (hpair : ∑ s, a s * pairContributionReal s = 1000000000 * pairValue)
    (hcongruence : ∑ s, a s * congruenceContributionReal s = 0) :
    (1062576034 / 1000000000 : ℝ) * δ + pairValue ≤
      (246993028 / 1000000000 : ℝ) := by
  have hnonneg : 0 ≤ ∑ s, a s * (certificateAtomInt s.val : ℝ) := by
    apply Finset.sum_nonneg
    intro s _
    by_cases hz : a s = 0
    · simp [hz]
    · apply mul_nonneg (ha s)
      exact_mod_cast hsupport s hz
  have hcast (s : AtomIndex) :
      (certificateAtomInt s.val : ℝ) =
        246993028 - 1062576034 * bitZeroIndicator s - pairContributionReal s +
          congruenceContributionReal s := by
    simp only [certificateAtomInt, bitZeroIndicator, pairContributionReal,
      congruenceContributionReal, Int.cast_add, Int.cast_sub, Int.cast_ofNat]
    split <;> norm_num
  simp_rw [hcast, mul_add, mul_sub] at hnonneg
  repeat' rw [Finset.sum_add_distrib] at hnonneg
  repeat' rw [Finset.sum_sub_distrib] at hnonneg
  have hconst : (∑ s, a s * (246993028 : ℝ)) = 246993028 := by
    rw [← Finset.sum_mul, htotal]
    norm_num
  have hvertex' : (∑ s, a s * (1062576034 * bitZeroIndicator s)) =
      1062576034 * δ := by
    calc
      (∑ s, a s * (1062576034 * bitZeroIndicator s)) =
          1062576034 * ∑ s, a s * bitZeroIndicator s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = 1062576034 * δ := by rw [hvertex]
  rw [hconst, hvertex', hpair, hcongruence] at hnonneg
  norm_num at hnonneg ⊢
  linarith

end Erdos232
