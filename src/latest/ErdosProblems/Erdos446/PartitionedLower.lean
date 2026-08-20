/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.LowerReduction

/-!
# Erdős Problem 446: partitioned analytic lower reduction

Ford applies the prime-cluster estimate separately to the disjoint vector
classes and only then joins their exact small-prime support cells.  This is
essential: applying Cauchy--Schwarz once to the union would discard the
reciprocal cyclic penalty which supplies the sharp lower bound.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- The lower reduction summed over pairwise-disjoint finite classes.

The denominator in every summand is positive for the nonempty squarefree
block classes used below.  Stating that fact as a hypothesis keeps this
lemma independent of the particular prime-block construction. -/
theorem ford_partitioned_cluster_lower_reduction
    {ι : Type*} [DecidableEq ι] {I : Finset ι}
    {N y B : ℕ} {A : ι → Finset ℕ}
    (hN : 3 ≤ N)
    (hprime : ∀ x : ℕ, N ≤ x →
      (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
      dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ))
    (hy : 0 < y) (hBy : B ≤ 2 * y)
    (hdisj : (I : Set ι).PairwiseDisjoint A)
    (hA : ∀ i ∈ I, ∀ a ∈ A i, 0 < a)
    (hbound : ∀ i ∈ I, ∀ a ∈ A i, a ≤ B)
    (hBsq : B * B < y)
    (hsq : ∀ i ∈ I, ∀ a ∈ A i, Squarefree a)
    (hscale : ∀ i ∈ I, ∀ a ∈ A i, ∀ d ∈ a.divisors,
      N ≤ y / d ∧ y ≤ (y / d) ^ 2)
    (hW : ∀ i ∈ I,
      0 < ∑ a ∈ A i, (closePairCount a : ℝ) / a) :
    smallPrimeEulerDensity (2 * y) *
        (∑ i ∈ I,
          (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
              (∑ a ∈ A i, (a.divisors.card : ℝ) / a) ^ 2) /
            (∑ a ∈ A i, (closePairCount a : ℝ) / a)) ≤
      epsilon y (2 * y) := by
  let U : Finset ℕ := I.biUnion A
  have hUpos : ∀ a ∈ U, 0 < a := by
    intro a ha
    obtain ⟨i, hiI, hai⟩ := Finset.mem_biUnion.mp ha
    exact hA i hiI a hai
  have hUbound : ∀ a ∈ U, a ≤ B := by
    intro a ha
    obtain ⟨i, hiI, hai⟩ := Finset.mem_biUnion.mp ha
    exact hbound i hiI a hai
  have hUsq : ∀ a ∈ U, Squarefree a := by
    intro a ha
    obtain ⟨i, hiI, hai⟩ := Finset.mem_biUnion.mp ha
    exact hsq i hiI a hai
  have hterm : ∀ i ∈ I,
      (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
          (∑ a ∈ A i, (a.divisors.card : ℝ) / a) ^ 2) /
        (∑ a ∈ A i, (closePairCount a : ℝ) / a) ≤
      ∑ a ∈ A i, (1 / (a : ℝ)) * eligiblePrimeMass y a := by
    intro i hi
    have hlocal := sum_eligiblePrimeMass_lower hN hprime
      (hA i hi) (hscale i hi)
    have hWpos := hW i hi
    exact (div_le_iff₀ hWpos).2 (by simpa [mul_assoc] using hlocal)
  have hsum :
      (∑ i ∈ I,
          (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
              (∑ a ∈ A i, (a.divisors.card : ℝ) / a) ^ 2) /
            (∑ a ∈ A i, (closePairCount a : ℝ) / a)) ≤
        ∑ a ∈ U, (1 / (a : ℝ)) * eligiblePrimeMass y a := by
    calc
      (∑ i ∈ I,
          (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
              (∑ a ∈ A i, (a.divisors.card : ℝ) / a) ^ 2) /
            (∑ a ∈ A i, (closePairCount a : ℝ) / a)) ≤
          ∑ i ∈ I, ∑ a ∈ A i,
            (1 / (a : ℝ)) * eligiblePrimeMass y a :=
        Finset.sum_le_sum hterm
      _ = ∑ a ∈ U, (1 / (a : ℝ)) * eligiblePrimeMass y a := by
        simpa only [U] using
          (Finset.sum_biUnion (f := fun a : ℕ ↦
            (1 / (a : ℝ)) * eligiblePrimeMass y a) hdisj).symm
  have hcrt := ford_moduli_lower hy hBy hUpos hUbound hBsq hUsq
  exact le_trans (mul_le_mul_of_nonneg_left hsum
    (smallPrimeEulerDensity_nonneg _)) hcrt

end Erdos446
