/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.SquarefreeQuadraticClasses
import ErdosProblems.Erdos822.IntegerResidueBlocks
import ErdosProblems.Erdos822.PrimeSquareAverage

/-!
# Large primes in the quadratic CRT classes

For a fixed squarefree common divisor, the medium-range argument needs only
the large prime variable.  This file packages the union of its possible CRT
classes and bounds its reciprocal mass by the number of quadratic roots
times the elementary integer-residue bound.
-/

namespace Erdos822

open scoped BigOperators

/-- Large-layer primes whose residue modulo h is one of the quadratic CRT
root classes. -/
noncomputable def quadraticLargePrimeClasses
    (N h u v y : ℕ) : Finset ℕ :=
  (quadraticAssignmentResidues u v h).biUnion fun a =>
    largePrimeResidueClass N h a y

@[simp]
theorem mem_quadraticLargePrimeClasses_iff
    {N h u v y q : ℕ} :
    q ∈ quadraticLargePrimeClasses N h u v y ↔
      ∃ a ∈ quadraticAssignmentResidues u v h,
        q ∈ largePrimeResidueClass N h a y := by
  simp [quadraticLargePrimeClasses]

/-- A large prime whose reduced residue is a quadratic assignment belongs
to the corresponding union of large-prime classes. -/
theorem mem_quadraticLargePrimeClasses_of_mod_mem
    {N h u v y q : ℕ}
    (hyN : y < N ^ 21)
    (hq : q ∈ largePrimes N)
    (hroot : q % h ∈ quadraticAssignmentResidues u v h) :
    q ∈ quadraticLargePrimeClasses N h u v y := by
  rw [mem_quadraticLargePrimeClasses_iff]
  refine ⟨q % h, hroot, ?_⟩
  rw [mem_largePrimeResidueClass_iff]
  have hqN : N ^ 21 ≤ q := (mem_largePrimes_iff.mp hq).1
  exact ⟨hq, hyN.trans_le hqN, by simp⟩

/-- The reciprocal mass of the whole quadratic union is at most its root
count times the one-class integer-residue estimate. -/
theorem sum_inv_quadraticLargePrimeClasses_le_card_mul
    {N h u v y : ℕ} (hN : 2 ≤ N) (hh : 0 < h) :
    ∑ q ∈ quadraticLargePrimeClasses N h u v y,
        (1 : ℝ) / q ≤
      ((quadraticAssignmentResidues u v h).card : ℝ) *
        (((1 : ℝ) / h + (1 : ℝ) / (N ^ 21 : ℕ)) *
          (harmonic N : ℝ)) := by
  classical
  let E : ℝ :=
    ((1 : ℝ) / h + (1 : ℝ) / (N ^ 21 : ℕ)) *
      (harmonic N : ℝ)
  have hE : 0 ≤ E := by
    dsimp [E]
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity
  calc
    (∑ q ∈ quadraticLargePrimeClasses N h u v y,
        (1 : ℝ) / q) ≤
        ∑ a ∈ quadraticAssignmentResidues u v h,
          ∑ q ∈ largePrimeResidueClass N h a y,
            (1 : ℝ) / q := by
      unfold quadraticLargePrimeClasses
      apply sum_biUnion_le_sum
      intro a ha q hq
      positivity
    _ ≤ ∑ a ∈ quadraticAssignmentResidues u v h, E := by
      apply Finset.sum_le_sum
      intro a ha
      dsimp [E]
      exact sum_inv_largePrimeResidueClass_le_harmonic_of_pos hN hh
    _ = ((quadraticAssignmentResidues u v h).card : ℝ) * E := by
      rw [Finset.sum_const]
      simp
    _ = ((quadraticAssignmentResidues u v h).card : ℝ) *
        (((1 : ℝ) / h + (1 : ℝ) / (N ^ 21 : ℕ)) *
          (harmonic N : ℝ)) := by rfl

/-- For a corrected common divisor, replace the root count by the honest
two-to-the-number-of-prime-factors bound. -/
theorem sum_inv_quadraticLargePrimeClasses_le_two_pow
    {N y h m m' u v : ℕ}
    (hN : 2 ≤ N) (hhpos : 0 < h)
    (hm : m ∈ squarefreeLargeGcdFreeOddCofactors N y)
    (hh : h ∣ shiftedCoefficientGcd m m')
    (hprimeLarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p) :
    ∑ q ∈ quadraticLargePrimeClasses N h u v y,
        (1 : ℝ) / q ≤
      ((2 ^ h.primeFactors.card : ℕ) : ℝ) *
        (((1 : ℝ) / h + (1 : ℝ) / (N ^ 21 : ℕ)) *
          (harmonic N : ℝ)) := by
  have hbase :=
    sum_inv_quadraticLargePrimeClasses_le_card_mul
      (N := N) (h := h) (u := u) (v := v) (y := y) hN hhpos
  have hcard :
      ((quadraticAssignmentResidues u v h).card : ℝ) ≤
        ((2 ^ h.primeFactors.card : ℕ) : ℝ) := by
    exact_mod_cast
      quadraticAssignments_card_le_two_pow_of_corrected_commonDivisor
        (u := u) (v := v) hm hh hprimeLarge
  have hfactor :
      0 ≤ (((1 : ℝ) / h + (1 : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ)) := by
    have hH : 0 ≤ (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      exact Finset.sum_nonneg fun j hj => by positivity
    positivity
  exact hbase.trans (mul_le_mul_of_nonneg_right hcard hfactor)

end Erdos822
