import Mathlib

open Filter Asymptotics
open scoped BigOperators Asymptotics Topology

namespace Erdos380

def largestPrimeFactor (n : ℕ) : ℕ := max 1 (n.primeFactors.sup id)

def intervalProduct (u v : ℕ) : ℕ := ∏ n ∈ Finset.Icc u v, n

def intervalPrime (u v : ℕ) : ℕ := largestPrimeFactor (intervalProduct u v)

def BadInterval (u v : ℕ) : Prop :=
  1 ≤ u ∧ u ≤ v ∧ 1 < intervalProduct u v ∧
    intervalPrime u v ^ 2 ∣ intervalProduct u v

def BadPoint (n : ℕ) : Prop :=
  ∃ u v : ℕ, BadInterval u v ∧ u ≤ n ∧ n ≤ v

noncomputable def badPointsUpTo (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter BadPoint

noncomputable def B (x : ℝ) : ℝ := ((badPointsUpTo ⌊x⌋₊).card : ℝ)

noncomputable def repeatedLargestPrimeUpTo (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => largestPrimeFactor n ^ 2 ∣ n

noncomputable def repeatedLargestPrimeCount (x : ℝ) : ℝ :=
  ((repeatedLargestPrimeUpTo ⌊x⌋₊).card : ℝ)

/-- The bad-interval counting function has the exact repeated-prime asymptotic. -/
theorem erdos_380 : B ~[Filter.atTop] repeatedLargestPrimeCount := by
  sorry

end Erdos380
