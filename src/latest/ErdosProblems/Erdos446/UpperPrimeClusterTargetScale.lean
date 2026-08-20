/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperPrimeClusterWindow

/-!
# Erdős Problem 446: cluster windows at a shell-dependent scale

In the complementary-factor case of Ford's Lemma 3.2 the divisor coordinate
is a dyadic shell scale `w`, while the varying logarithmic denominator is
normalized at the original scale `y`.  This file proves the exact uniform
form of the short-prime estimate needed in that situation.  The sole scale
condition is the one used in Ford's proof, `y^(2/3) ≤ w`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

noncomputable section

theorem fordVariableLogArgument_target_le_two_mul_prime
    {X y w a p : ℕ} (hy : 1 ≤ y)
    (hyw : (y : ℝ) ^ (2 / 3 : ℝ) ≤ (w : ℝ))
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X w (2 * w)) :
    fordVariableLogArgument y a.primeFactors ≤ 2 * (p : ℝ) := by
  have hdata := mem_fordAdmissibleLargestPrimePairs.mp hap
  have haPos : 0 < a := hdata.1
  have hpPos : 0 < p := hdata.2.2.2.1.pos
  have haSq : Squarefree a := hdata.2.2.2.2.1
  obtain ⟨d, hd, hwdp, _hdp⟩ := hdata.2.2.2.2.2.2.2
  have hdPos := Nat.pos_of_mem_divisors hd
  have hdDvd := Nat.dvd_of_mem_divisors hd
  have hdLeA : d ≤ a := Nat.le_of_dvd haPos hdDvd
  have hwR : (w : ℝ) < (d : ℝ) * (p : ℝ) := by
    exact_mod_cast hwdp
  have hapR : (d : ℝ) * (p : ℝ) ≤ (a : ℝ) * (p : ℝ) := by
    gcongr
  have haR : (0 : ℝ) < a := by exact_mod_cast haPos
  have hfirst : (y : ℝ) ^ (2 / 3 : ℝ) / (a : ℝ) ≤ p := by
    rw [div_le_iff₀ haR]
    simpa [mul_comm] using hyw.trans (hwR.le.trans hapR)
  have hprod : a.primeFactors.prod id = a := by
    simpa using Nat.prod_primeFactors_of_squarefree haSq
  have hmax : primeSupportMax a.primeFactors ≤ p := by
    by_cases hS : a.primeFactors.Nonempty
    · have hmem := primeSupportMax_mem hS
      have hprime := Nat.prime_of_mem_primeFactors hmem
      exact (hdata.2.2.2.2.2.1 _ hprime
        (Nat.dvd_of_mem_primeFactors hmem)).le
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [primeSupportMax, hempty]
  unfold fordVariableLogArgument
  rw [hprod]
  have hmaxR : (primeSupportMax a.primeFactors : ℝ) ≤ p := by
    exact_mod_cast hmax
  nlinarith

theorem one_lt_fordVariableLogArgument_target
    {X y w a p : ℕ} (hy : 2 ≤ y)
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X w (2 * w)) :
    1 < fordVariableLogArgument y a.primeFactors := by
  have hdata := mem_fordAdmissibleLargestPrimePairs.mp hap
  have haSq : Squarefree a := hdata.2.2.2.2.1
  have hprod : a.primeFactors.prod id = a := by
    simpa using Nat.prod_primeFactors_of_squarefree haSq
  by_cases hS : a.primeFactors.Nonempty
  · have hpmax : (primeSupportMax a.primeFactors).Prime :=
      Nat.prime_of_mem_primeFactors (primeSupportMax_mem hS)
    have hmaxTwo : (2 : ℝ) ≤ primeSupportMax a.primeFactors := by
      exact_mod_cast hpmax.two_le
    unfold fordVariableLogArgument
    exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      (hmaxTwo.trans (le_add_of_nonneg_left (by positivity)))
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hS
    have haOne : a = 1 := by
      rw [← hprod, hempty]
      simp
    have hyOne : (1 : ℝ) < y := by
      exact_mod_cast (show 1 < y by omega)
    have hpow : 1 < (y : ℝ) ^ (2 / 3 : ℝ) :=
      Real.one_lt_rpow hyOne (by norm_num)
    unfold fordVariableLogArgument
    rw [hempty]
    simpa [primeSupportMax] using hpow

theorem log_fordVariableLogArgument_target_le_two_log_prime
    {X y w a p : ℕ} (hy : 2 ≤ y)
    (hyw : (y : ℝ) ^ (2 / 3 : ℝ) ≤ (w : ℝ))
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X w (2 * w)) :
    Real.log (fordVariableLogArgument y a.primeFactors) ≤
      2 * Real.log (p : ℝ) := by
  have hpPrime := (mem_fordAdmissibleLargestPrimePairs.mp hap).2.2.2.1
  have hargPos : 0 < fordVariableLogArgument y a.primeFactors :=
    (one_lt_fordVariableLogArgument_target hy hap).trans' zero_lt_one
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hmono : Real.log (fordVariableLogArgument y a.primeFactors) ≤
      Real.log ((2 : ℝ) * p) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using hargPos)
      (by simpa only [Set.mem_Ioi] using mul_pos (by norm_num) hpR)
      (fordVariableLogArgument_target_le_two_mul_prime (by omega) hyw hap)
  rw [Real.log_mul (by norm_num) hpR.ne'] at hmono
  have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hpPrime.two_le)
  linarith

theorem fordAdmissiblePrimeFiberBin_target_log_weight_le
    {K : ℝ} (hK : 0 < K)
    (hmass : ∀ Q : Finset ℕ,
      (∀ p ∈ Q, p.Prime) →
      (∀ p ∈ Q, ∀ q ∈ Q, p ≤ 4 * q) →
      ∀ q ∈ Q, primeSetMass Q ≤ K / Real.log (q : ℝ))
    {X y w a j : ℕ} (hy : 2 ≤ y)
    (hyw : (y : ℝ) ^ (2 / 3 : ℝ) ≤ (w : ℝ))
    (hj : j ∈ fordWitnessBins X w a) :
    (∑ p ∈ fordAdmissiblePrimeFiberBin X w a j,
        1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
      4 * K / Real.log (fordVariableLogArgument y a.primeFactors) ^ 2 := by
  obtain ⟨q, hqFiber, hqLog⟩ := mem_fordWitnessBins.mp hj
  have hqBin : q ∈ fordAdmissiblePrimeFiberBin X w a j :=
    mem_fordAdmissiblePrimeFiberBin.mpr ⟨hqFiber, hqLog⟩
  have hqPair := (mem_fordAdmissiblePrimeFiber.mp hqFiber).2.2
  have hargOne := one_lt_fordVariableLogArgument_target hy hqPair
  have hargLog : 0 < Real.log (fordVariableLogArgument y a.primeFactors) :=
    Real.log_pos hargOne
  let Q := fordAdmissiblePrimeFiberBin X w a j
  have hprime : ∀ p ∈ Q, p.Prime := by
    intro p hp
    exact (mem_fordAdmissiblePrimeFiber.mp
      (mem_fordAdmissiblePrimeFiberBin.mp hp).1).1
  have hcomp : ∀ p ∈ Q, ∀ q ∈ Q, p ≤ 4 * q := by
    intro p hp q hq
    exact fordAdmissiblePrimeFiberBin_comparable hp hq
  have hpoint : ∀ p ∈ Q,
      1 / ((p : ℝ) * Real.log (p : ℝ)) ≤
        (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
          (1 / (p : ℝ)) := by
    intro p hp
    have hpPrime := hprime p hp
    have hpLog : 0 < Real.log (p : ℝ) := hpPrime.log_pos
    have hpPair := (mem_fordAdmissiblePrimeFiber.mp
      (mem_fordAdmissiblePrimeFiberBin.mp hp).1).2.2
    have hlogCompare :=
      log_fordVariableLogArgument_target_le_two_log_prime hy hyw hpPair
    have hinv : 1 / Real.log (p : ℝ) ≤
        2 / Real.log (fordVariableLogArgument y a.primeFactors) := by
      rw [div_le_div_iff₀ hpLog hargLog]
      linarith
    calc
      1 / ((p : ℝ) * Real.log (p : ℝ)) =
          (1 / (p : ℝ)) * (1 / Real.log (p : ℝ)) := by ring
      _ ≤ (1 / (p : ℝ)) *
          (2 / Real.log (fordVariableLogArgument y a.primeFactors)) := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
          (1 / (p : ℝ)) := by ring
  have hsum :
      (∑ p ∈ Q, 1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
        (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
          primeSetMass Q := by
    calc
      (∑ p ∈ Q, 1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
          ∑ p ∈ Q,
            (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
              (1 / (p : ℝ)) :=
        Finset.sum_le_sum fun p hp ↦ hpoint p hp
      _ = (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
          primeSetMass Q := by
        rw [primeSetMass, Finset.mul_sum]
  have hqPrime := hprime q hqBin
  have hqLogPos : 0 < Real.log (q : ℝ) := hqPrime.log_pos
  have hqMass := hmass Q hprime hcomp q hqBin
  have hqCompare :=
    log_fordVariableLogArgument_target_le_two_log_prime hy hyw hqPair
  have hmassArg : primeSetMass Q ≤
      2 * K / Real.log (fordVariableLogArgument y a.primeFactors) := by
    apply hqMass.trans
    rw [div_le_div_iff₀ hqLogPos hargLog]
    nlinarith
  calc
    (∑ p ∈ fordAdmissiblePrimeFiberBin X w a j,
        1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
      (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
        primeSetMass Q := hsum
    _ ≤ (2 / Real.log (fordVariableLogArgument y a.primeFactors)) *
        (2 * K / Real.log (fordVariableLogArgument y a.primeFactors)) := by
      exact mul_le_mul_of_nonneg_left hmassArg (by positivity)
    _ = 4 * K /
        Real.log (fordVariableLogArgument y a.primeFactors) ^ 2 := by ring

/-- Short-prime cluster bound at a shell scale `w`, but with Ford's varying
denominator retained at the original scale `y`. -/
theorem exists_pos_admissiblePrimeFiber_target_log_weight_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y w X a : ℕ, 2 ≤ y →
      (y : ℝ) ^ (2 / 3 : ℝ) ≤ (w : ℝ) →
      (∑ p ∈ fordAdmissiblePrimeFiber X w (2 * w) a,
        1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
      C * clusterLength a /
        Real.log (fordVariableLogArgument y a.primeFactors) ^ 2 := by
  obtain ⟨K, hK, hmass⟩ := exists_pos_comparable_primeSetMass_upper
  let C : ℝ := 8 * K / Real.log 2
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun y w X a hy hyw ↦ ?_⟩
  by_cases hB : (fordWitnessBins X w a).Nonempty
  · obtain ⟨j₀, hj₀⟩ := hB
    obtain ⟨q₀, hq₀Fiber, _hq₀Log⟩ := mem_fordWitnessBins.mp hj₀
    have hq₀Pair := (mem_fordAdmissiblePrimeFiber.mp hq₀Fiber).2.2
    have hargLog : 0 <
        Real.log (fordVariableLogArgument y a.primeFactors) :=
      Real.log_pos (one_lt_fordVariableLogArgument_target hy hq₀Pair)
    have hbins := fordWitnessBins_card_mul_log_two_le_two_clusterLength
      X w a
    rw [sum_fordAdmissiblePrimeFiber_eq_bins]
    calc
      (∑ j ∈ fordWitnessBins X w a,
          ∑ p ∈ fordAdmissiblePrimeFiberBin X w a j,
            1 / ((p : ℝ) * Real.log (p : ℝ))) ≤
        ∑ _j ∈ fordWitnessBins X w a,
          4 * K /
            Real.log (fordVariableLogArgument y a.primeFactors) ^ 2 := by
        exact Finset.sum_le_sum fun j hj ↦
          fordAdmissiblePrimeFiberBin_target_log_weight_le
            hK hmass hy hyw hj
      _ = ((fordWitnessBins X w a).card : ℝ) *
          (4 * K /
            Real.log (fordVariableLogArgument y a.primeFactors) ^ 2) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ C * clusterLength a /
          Real.log (fordVariableLogArgument y a.primeFactors) ^ 2 := by
        rw [← mul_div_assoc]
        rw [div_le_div_iff₀ (sq_pos_of_pos hargLog)
          (sq_pos_of_pos hargLog)]
        dsimp [C]
        field_simp [hlogTwo.ne']
        nlinarith
  · have hBempty := Finset.not_nonempty_iff_eq_empty.mp hB
    have hFiberEmpty : fordAdmissiblePrimeFiber X w (2 * w) a = ∅ := by
      rw [← biUnion_fordAdmissiblePrimeFiberBins X w a, hBempty]
      simp
    rw [hFiberEmpty]
    simp only [Finset.sum_empty, zero_le]
    exact div_nonneg
      (mul_nonneg hC.le (clusterLength_nonneg a)) (sq_nonneg _)

end

end Erdos446
