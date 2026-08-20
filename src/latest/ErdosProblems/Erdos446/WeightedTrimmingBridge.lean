/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperExceptionalMassBridge
import ErdosProblems.Erdos446.WeightedOccupancyBridge

/-!
# Erdős Problem 446: bounded-cell weighted occupancy mass

This is the abstract bridge used after trimming every prime block to mass at
most `log 2`.  Once every cell has mass at most a common nonnegative bound
`L`, an arbitrary occupancy subfamily costs at most `L^k` times its original
reciprocal-factorial mass.  In particular the full exceptional/crowding
cover can then be used without a pointwise exponential error.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem weightedCompositionMass_le_const_pow
    {v k : ℕ} {lam : Fin v → ℝ} {L : ℝ}
    (hlamNonneg : ∀ i, 0 ≤ lam i)
    (hlam : ∀ i, lam i ≤ L) {b : Fin v → ℕ}
    (hsum : ∑ i, b i = k) :
    weightedCompositionMass lam b ≤
      L ^ k / compositionFactorial b := by
  rw [weightedCompositionMass]
  apply div_le_div_of_nonneg_right _ (by
    dsimp [compositionFactorial]
    positivity)
  calc
    ∏ i : Fin v, lam i ^ b i ≤ ∏ i : Fin v, L ^ b i := by
      apply Finset.prod_le_prod
      · intro i hi
        exact pow_nonneg (hlamNonneg i) _
      · intro i hi
        exact pow_le_pow_left₀ (hlamNonneg i) (hlam i) _
    _ = L ^ (∑ i, b i) := by rw [← Finset.prod_pow_eq_pow_sum]
    _ = L ^ k := by rw [hsum]

/-- The sharp reciprocal-factorial comparison for every subfamily of
`compositionsOf v k`; no monotonicity property of the family is needed. -/
theorem weightedOccupancyMassOver_le_const_pow_reciprocalFactorialMass
    {v k : ℕ} {lam : Fin v → ℝ} {L : ℝ}
    (hlamNonneg : ∀ i, 0 ≤ lam i)
    (hlam : ∀ i, lam i ≤ L) {I : Finset (Fin v → ℕ)}
    (hI : I ⊆ compositionsOf v k) :
    weightedOccupancyMassOver lam I ≤
      L ^ k * reciprocalFactorialMassOver I := by
  rw [weightedOccupancyMassOver, reciprocalFactorialMassOver,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  have hsum : ∑ i, b i = k := mem_compositionsOf.mp (hI hb)
  calc
    weightedCompositionMass lam b ≤
        L ^ k / compositionFactorial b :=
      weightedCompositionMass_le_const_pow hlamNonneg hlam hsum
    _ = L ^ k * (1 / compositionFactorial b) := by ring

/-- Specialization at the retained prime-block cap. -/
theorem weightedOccupancyMassOver_le_logTwo_pow
    {v k : ℕ} {lam : Fin v → ℝ}
    (hlamNonneg : ∀ i, 0 ≤ lam i)
    (hlam : ∀ i, lam i ≤ Real.log 2)
    {I : Finset (Fin v → ℕ)} (hI : I ⊆ compositionsOf v k) :
    weightedOccupancyMassOver lam I ≤
      Real.log 2 ^ k * reciprocalFactorialMassOver I := by
  exact weightedOccupancyMassOver_le_const_pow_reciprocalFactorialMass
    hlamNonneg hlam hI

end Erdos446
