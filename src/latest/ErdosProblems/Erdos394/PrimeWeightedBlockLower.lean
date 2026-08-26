import ErdosProblems.Erdos394.GoodPrimeMass
import ErdosProblems.Erdos394.PrimeReciprocal

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Chebyshev lower bound for weighted prime blocks
-/

open Nat Finset Filter Asymptotics

namespace Erdos394

/-- Reciprocal sum on `(A,U]` is the difference of endpoint sums. -/
theorem sum_largePrimeInterval_one_div
    {A U : ℕ} (hAU : A ≤ U) :
    (∑ p ∈ largePrimeInterval A U, (1 / (p : ℝ))) =
      primeReciprocalSum U - primeReciprocalSum A := by
  have hsub : A.primesLE ⊆ U.primesLE := Nat.primesLE_mono hAU
  have hs := Finset.sum_sdiff hsub (f := fun p : ℕ ↦ (1 / (p : ℝ)))
  unfold largePrimeInterval primeReciprocalSum
  linarith

/-- A reciprocal lower bound on `(N,16N]` gives a weighted-prime lower bound
larger by `N²`. -/
theorem mul_sq_reciprocalBlock_le_primeIntervalWeightedMass
    {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ^ 2 *
        (primeReciprocalSum (16 * N) - primeReciprocalSum N) ≤
      primeIntervalWeightedMass N (16 * N) := by
  rw [← sum_largePrimeInterval_one_div (show N ≤ 16 * N by omega)]
  unfold primeIntervalWeightedMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpN := (mem_largePrimeInterval_iff.mp hp).1
  have hpprime := (mem_largePrimeInterval_iff.mp hp).2.2
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  rw [show (N : ℝ) ^ 2 * (1 / (p : ℝ)) = (N : ℝ) ^ 2 / p by ring]
  apply (div_le_iff₀ hpR).2
  have hpNR : (N : ℝ) ≤ p := by exact_mod_cast hpN.le
  nlinarith

/-- Finite weighted block lower bound from the standard reciprocal block
estimate. -/
theorem log_two_mul_sq_div_le_primeIntervalWeightedMass
    {N : ℕ} (hN : 0 < N)
    (hrecip : Real.log 2 / (16 * Real.log N) ≤
      primeReciprocalSum (16 * N) - primeReciprocalSum N) :
    Real.log 2 * (N : ℝ) ^ 2 / (16 * Real.log N) ≤
      primeIntervalWeightedMass N (16 * N) := by
  have hN2 : 0 ≤ (N : ℝ) ^ 2 := by positivity
  calc
    Real.log 2 * (N : ℝ) ^ 2 / (16 * Real.log N) =
        (N : ℝ) ^ 2 * (Real.log 2 / (16 * Real.log N)) := by ring
    _ ≤ (N : ℝ) ^ 2 *
        (primeReciprocalSum (16 * N) - primeReciprocalSum N) :=
      mul_le_mul_of_nonneg_left hrecip hN2
    _ ≤ primeIntervalWeightedMass N (16 * N) :=
      mul_sq_reciprocalBlock_le_primeIntervalWeightedMass hN

/-- Eventually every block `(N,16N]` has weighted prime mass
`≫N²/log N`, with an explicit constant. -/
theorem eventually_weightedPrimeBlock_lower :
    ∀ᶠ N : ℕ in atTop,
      Real.log 2 * (N : ℝ) ^ 2 / (16 * Real.log N) ≤
        primeIntervalWeightedMass N (16 * N) := by
  filter_upwards [eventually_gt_atTop 0,
    eventually_primeReciprocal_block_lower] with N hN hrecip
  exact log_two_mul_sq_div_le_primeIntervalWeightedMass hN hrecip

end Erdos394
