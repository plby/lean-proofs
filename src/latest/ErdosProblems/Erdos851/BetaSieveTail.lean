/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Numerical tails for the beta-sieve fundamental lemma

This file contains no sieve combinatorics.  It packages the numerical step
used after the boundary-chain argument: if chains of length `r` have normalized
mass at most `A * C^r / r!`, then the contribution of all chains beginning at
a sufficiently large depth is arbitrarily small.

For the application to Erdős problem 851 we fix beta to `100` and dimension at
most two.  The factor `200` in `beta100ChainMajorant` is therefore
`beta * kappa`; the remaining natural parameter `c` is the constant furnished
by the dimension estimate and the lower bound for the least prime in a
boundary chain.
-/

namespace Erdos851

open Filter
open scoped BigOperators Topology

namespace BetaSieveTail

/-- The fixed beta used by the numerical beta-sieve estimates. -/
def beta : ℕ := 100

/-- The largest sieve dimension needed for one- and two-shift counts. -/
def maxDimension : ℕ := 2

/-- The exponential-series majorant `C^n / n!`. -/
noncomputable def factorialMajorant (C n : ℕ) : ℝ :=
  (C : ℝ) ^ n / (n.factorial : ℝ)

/-- The beta-100, dimension-at-most-two chain majorant. -/
noncomputable def beta100ChainMajorant (c n : ℕ) : ℝ :=
  factorialMajorant (beta * maxDimension * c) n

@[simp] theorem beta_mul_maxDimension : beta * maxDimension = 200 := by
  norm_num [beta, maxDimension]

theorem factorialMajorant_nonneg (C n : ℕ) :
    0 ≤ factorialMajorant C n := by
  unfold factorialMajorant
  positivity

/-- The elementary factorial estimate behind the geometric tail comparison. -/
theorem factorial_mul_succ_pow_le_factorial_add (s i : ℕ) :
    (s.factorial : ℝ) * (s + 1 : ℕ) ^ i ≤ ((s + i).factorial : ℝ) := by
  exact_mod_cast (Nat.factorial_mul_pow_le_factorial (m := s) (n := i))

/-- The exact ratio between successive terms of the factorial majorant. -/
theorem factorialMajorant_succ (C n : ℕ) :
    factorialMajorant C (n + 1) =
      factorialMajorant C n * (C : ℝ) / (n + 1 : ℕ) := by
  unfold factorialMajorant
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  field_simp

/-- Past `2*C`, consecutive factorial-majorant terms are dominated by a
geometric sequence of ratio `1/2`. -/
theorem factorialMajorant_add_le_geometric
    {C s : ℕ} (hs : 2 * C ≤ s + 1) (i : ℕ) :
    factorialMajorant C (s + i) ≤
      factorialMajorant C s * (1 / 2 : ℝ) ^ i := by
  induction i with
  | zero => simp
  | succ i hi =>
      have hdenNat : 2 * C ≤ s + i + 1 := by omega
      have hden : (0 : ℝ) < (s + i + 1 : ℕ) := by positivity
      have hratio : (C : ℝ) / (s + i + 1 : ℕ) ≤ 1 / 2 := by
        rw [div_le_iff₀ hden]
        have hdenReal : 2 * (C : ℝ) ≤ (s + i + 1 : ℕ) := by
          exact_mod_cast hdenNat
        linarith
      rw [Nat.add_succ, factorialMajorant_succ]
      calc
        factorialMajorant C (s + i) * (C : ℝ) / (s + i + 1 : ℕ) =
            factorialMajorant C (s + i) *
              ((C : ℝ) / (s + i + 1 : ℕ)) := by ring
        _ ≤ (factorialMajorant C s * (1 / 2 : ℝ) ^ i) *
              ((C : ℝ) / (s + i + 1 : ℕ)) := by
          exact mul_le_mul_of_nonneg_right hi (by positivity)
        _ ≤ (factorialMajorant C s * (1 / 2 : ℝ) ^ i) * (1 / 2) := by
          exact mul_le_mul_of_nonneg_left hratio
            (mul_nonneg (factorialMajorant_nonneg C s) (by positivity))
        _ = factorialMajorant C s * (1 / 2 : ℝ) ^ (i + 1) := by
          rw [pow_succ]
          ring

/-- Every finite factorial tail is at most twice its first term once the
geometric regime has begun. -/
theorem sum_factorialMajorant_add_le
    {C s m : ℕ} (hs : 2 * C ≤ s + 1) :
    ∑ i ∈ Finset.range m, factorialMajorant C (s + i) ≤
      2 * factorialMajorant C s := by
  calc
    ∑ i ∈ Finset.range m, factorialMajorant C (s + i) ≤
        ∑ i ∈ Finset.range m,
          factorialMajorant C s * (1 / 2 : ℝ) ^ i := by
      apply Finset.sum_le_sum
      intro i hi
      exact factorialMajorant_add_le_geometric hs i
    _ = factorialMajorant C s *
        ∑ i ∈ Finset.range m, (1 / 2 : ℝ) ^ i := by
      rw [Finset.mul_sum]
    _ ≤ factorialMajorant C s * 2 := by
      exact mul_le_mul_of_nonneg_left (sum_geometric_two_le m)
        (factorialMajorant_nonneg C s)
    _ = 2 * factorialMajorant C s := by ring

/-- The first term of the factorial tail tends to zero. -/
theorem tendsto_factorialMajorant_zero (C : ℕ) :
    Tendsto (factorialMajorant C) atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (C : ℝ) ^ n / (n.factorial : ℝ)) atTop (nhds 0)
  exact FloorSemiring.tendsto_pow_div_factorial_atTop (C : ℝ)

/-- There is an arbitrarily deep odd truncation in the geometric regime for
which the normalized factorial tail is at most `eta`. -/
theorem exists_odd_factorial_tail_le
    (C : ℕ) {A eta : ℝ} (hA : 0 ≤ A) (heta : 0 < eta) :
    ∃ s : ℕ, Odd s ∧ 2 * C ≤ s + 1 ∧
      2 * A * factorialMajorant C s ≤ eta := by
  have hAone : 0 < A + 1 := by linarith
  have htarget : 0 < eta / (2 * (A + 1)) := by positivity
  have hevent : ∀ᶠ n : ℕ in atTop,
      factorialMajorant C n < eta / (2 * (A + 1)) :=
    (tendsto_order.1 (tendsto_factorialMajorant_zero C)).2 _ htarget
  rw [eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  let s := 2 * max N C + 1
  refine ⟨s, ?_, ?_, ?_⟩
  · exact ⟨max N C, by simp [s]⟩
  · dsimp [s]
    omega
  · have hsN : N ≤ s := by
      dsimp [s]
      omega
    have hsmall := hN s hsN
    have hsNonneg := factorialMajorant_nonneg C s
    have hmajor :
        2 * A * factorialMajorant C s ≤
          2 * (A + 1) * factorialMajorant C s := by
      nlinarith
    have hpos : 0 < 2 * (A + 1) := by positivity
    exact le_of_lt <| calc
      2 * A * factorialMajorant C s ≤
          2 * (A + 1) * factorialMajorant C s := hmajor
      _ < 2 * (A + 1) * (eta / (2 * (A + 1))) :=
        mul_lt_mul_of_pos_left hsmall hpos
      _ = eta := by field_simp

/-- Abstract absorption of a finite boundary-chain error.  The hypothesis
`hdimension` is the output of the dimension estimate together with the lower
bound for the least prime in each boundary chain; `hboundary` is the purely
combinatorial assertion that the normalized sieve error injects into those
chains. -/
theorem normalizedError_le_of_boundaryChain_bounds
    {C s m : ℕ} {A eta normalizedError : ℝ}
    {chainMass : ℕ → ℝ}
    (hA : 0 ≤ A) (hs : 2 * C ≤ s + 1)
    (hdimension : ∀ i < m,
      chainMass (s + i) ≤ A * factorialMajorant C (s + i))
    (hboundary : normalizedError ≤
      ∑ i ∈ Finset.range m, chainMass (s + i))
    (hsmall : 2 * A * factorialMajorant C s ≤ eta) :
    normalizedError ≤ eta := by
  calc
    normalizedError ≤
        ∑ i ∈ Finset.range m, chainMass (s + i) := hboundary
    _ ≤ ∑ i ∈ Finset.range m,
        A * factorialMajorant C (s + i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hdimension i (Finset.mem_range.mp hi)
    _ = A * ∑ i ∈ Finset.range m,
        factorialMajorant C (s + i) := by
      rw [Finset.mul_sum]
    _ ≤ A * (2 * factorialMajorant C s) := by
      gcongr
      exact sum_factorialMajorant_add_le hs
    _ = 2 * A * factorialMajorant C s := by ring
    _ ≤ eta := hsmall

/-- Beta `100` and dimension at most two: after a sufficiently large odd
depth, every finite boundary-chain error satisfying the `A,c` factorial
dimension bound is at most `eta`. -/
theorem exists_odd_beta100_normalizedError_le
    (c : ℕ) {A eta : ℝ} (hA : 0 ≤ A) (heta : 0 < eta) :
    ∃ s : ℕ, Odd s ∧
      2 * (beta * maxDimension * c) ≤ s + 1 ∧
      ∀ (m : ℕ) (chainMass : ℕ → ℝ) (normalizedError : ℝ),
        (∀ i < m, chainMass (s + i) ≤
          A * beta100ChainMajorant c (s + i)) →
        normalizedError ≤ ∑ i ∈ Finset.range m, chainMass (s + i) →
        normalizedError ≤ eta := by
  obtain ⟨s, hsOdd, hsGeom, hsSmall⟩ :=
    exists_odd_factorial_tail_le (beta * maxDimension * c) hA heta
  refine ⟨s, hsOdd, hsGeom, ?_⟩
  intro m chainMass normalizedError hdimension hboundary
  exact normalizedError_le_of_boundaryChain_bounds hA hsGeom
    (by simpa [beta100ChainMajorant] using hdimension)
    hboundary hsSmall

end BetaSieveTail

end Erdos851
