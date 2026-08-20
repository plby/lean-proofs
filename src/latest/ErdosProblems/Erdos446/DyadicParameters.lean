/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SizedDyadicLowerCore
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Erdős Problem 446: fixed dyadic parameters

All errors depending on the initial block index are a fixed polynomial
divided by `2^M`.  This file chooses one cutoff `M` which simultaneously
discharges the Mertens error, without-replacement loss, prime-selection
condition, and close-pair exponential budget.
-/

namespace Erdos446

open Filter Finset Real Asymptotics
open scoped BigOperators Topology

theorem tendsto_nat_pow_div_two_pow (d : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ d / (2 : ℝ) ^ n)
      atTop (nhds 0) := by
  exact (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) d
    (by norm_num : (1 : ℝ) < 2)).tendsto_div_nhds_zero

theorem blockEndpoint_ge_index (j : ℕ) : j ≤ blockEndpoint j := by
  have hj : j < 2 ^ j := j.lt_two_pow_self
  exact hj.le.trans (by
    dsimp [blockEndpoint]
    exact Nat.pow_le_pow_right (by omega) (by omega : j ≤ 2 ^ j))

theorem fordConstructionBound_ge_M {M K : ℕ} (hK : 0 < K) :
    M ≤ fordConstructionBound M K := by
  have hM : M < 2 ^ M := M.lt_two_pow_self
  have hexp : M ≤ 32 * 2 ^ (M + K) := by
    exact hM.le.trans (by
      have hpow : 2 ^ M ≤ 2 ^ (M + K) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact hpow.trans (Nat.le_mul_of_pos_left _ (by omega : 0 < 32)))
  exact hexp.trans (by
    have := Nat.le_of_lt (32 * 2 ^ (M + K)).lt_two_pow_self
    simpa [fordConstructionBound] using this)

theorem capped_selection_condition
    {M K : ℕ} (hM : 1 ≤ M)
    (hsmall : 2 * (M : ℝ) ^ 2 / (2 : ℝ) ^ M ≤ Real.log 2 / 2)
    (hhalf : ∀ i : Fin K,
      Real.log 2 / 2 ≤ primeBlockMass (M + i)) :
    ∀ b ∈ cappedCompositions M K, ∀ i : Fin K,
      (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
        primeBlockMass (M + i) := by
  intro b hb i
  have hcap := (mem_cappedCompositions.mp hb).2 i
  have hiPow : i.val + 1 ≤ 2 ^ (i.val + 1) :=
    Nat.le_of_lt (i.val + 1).lt_two_pow_self
  have hbi : b i ≤ 2 * M ^ 2 * 2 ^ i.val := by
    calc
      b i ≤ M * (M + i.val) := hcap
      _ ≤ M ^ 2 * (i.val + 1) := by
        have hMM : M ≤ M * M := by
          calc
            M = M * 1 := by omega
            _ ≤ M * M := Nat.mul_le_mul_left M hM
        have hiMM := Nat.mul_le_mul_right i.val hMM
        rw [pow_two]
        nlinarith
      _ ≤ M ^ 2 * 2 ^ (i.val + 1) :=
        Nat.mul_le_mul_left _ hiPow
      _ = 2 * M ^ 2 * 2 ^ i.val := by rw [pow_succ]; ring
  have hendpoint : (2 : ℝ) ^ (M + i.val) ≤
      (blockEndpoint (M + i) : ℝ) := by
    exact_mod_cast (show 2 ^ (M + i.val) ≤ blockEndpoint (M + i.val) by
      dsimp [blockEndpoint]
      exact Nat.pow_le_pow_right (by omega)
        (Nat.le_of_lt (M + i.val).lt_two_pow_self))
  have hden : (0 : ℝ) < (2 : ℝ) ^ (M + i.val) := by positivity
  have hendpointPos : (0 : ℝ) < blockEndpoint (M + i) := by
    exact_mod_cast blockEndpoint_pos (M + i.val)
  calc
    (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
        ((2 * M ^ 2 * 2 ^ i.val : ℕ) : ℝ) *
          (1 / (blockEndpoint (M + i) : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hbi) (by positivity)
    _ ≤ ((2 * M ^ 2 * 2 ^ i.val : ℕ) : ℝ) *
          (1 / (2 : ℝ) ^ (M + i.val)) := by
      apply mul_le_mul_of_nonneg_left
      · exact one_div_le_one_div_of_le hden hendpoint
      · positivity
    _ = 2 * (M : ℝ) ^ 2 / (2 : ℝ) ^ M := by
      push_cast
      rw [pow_add]
      field_simp
    _ ≤ Real.log 2 / 2 := hsmall
    _ ≤ primeBlockMass (M + i) := hhalf i

theorem exists_ford_fixed_parameters :
    ∃ N M : ℕ, ∃ C : ℝ,
      3 ≤ N ∧ 3 ≤ M ∧ N ≤ M ∧ 0 < C ∧
      (∀ x : ℕ, N ≤ x →
        (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
        dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ)) ∧
      (∀ j : ℕ, M ≤ j →
        |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j) ∧
      C / (2 : ℝ) ^ M ≤ Real.log 2 / 2 ∧
      2 * (M : ℝ) ^ 2 / (2 : ℝ) ^ M ≤ Real.log 2 / 2 ∧
      (4 * (M * M) * C + 12 * (M * M) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ M) ≤ 1 / 2 ∧
      4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ 1 := by
  obtain ⟨C, hC, hmassEv⟩ := exists_primeBlockMass_geometric_error
  obtain ⟨N, hprime⟩ := Filter.eventually_atTop.mp eventually_dyadicPrimeMass_bounds
  obtain ⟨J, hmass⟩ := Filter.eventually_atTop.mp hmassEv
  have hCzero : Tendsto (fun m : ℕ ↦ C / (2 : ℝ) ^ m)
      atTop (nhds 0) := by
    have hp : Tendsto (fun m : ℕ ↦ (2 : ℝ) ^ m) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    simpa [div_eq_mul_inv] using hp.inv_tendsto_atTop.const_mul C
  have hM2zero : Tendsto
      (fun m : ℕ ↦ 2 * (m : ℝ) ^ 2 / (2 : ℝ) ^ m)
      atTop (nhds 0) := by
    simpa [mul_div_assoc] using
      (tendsto_nat_pow_div_two_pow 2).const_mul 2
  have hM4zero := tendsto_nat_pow_div_two_pow 4
  have hbudgetZero : Tendsto
      (fun m : ℕ ↦
        (4 * (m * m) * C + 12 * (m * m) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ m)) atTop (nhds 0) := by
    have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have heq : (fun m : ℕ ↦
        (4 * (m * m) * C + 12 * (m * m) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ m)) =
        fun m : ℕ ↦
          (4 * C / Real.log 2) * ((m : ℝ) ^ 2 / (2 : ℝ) ^ m) +
          (12 / Real.log 2) * ((m : ℝ) ^ 4 / (2 : ℝ) ^ m) := by
      funext m
      push_cast
      rw [show ((m : ℝ) * m) ^ 2 = (m : ℝ) ^ 4 by ring]
      field_simp [hlog]
    rw [heq]
    simpa using
      ((tendsto_nat_pow_div_two_pow 2).const_mul (4 * C / Real.log 2)).add
        (hM4zero.const_mul (12 / Real.log 2))
  have hEZero : Tendsto
      (fun m : ℕ ↦ 4 * (m * m) * (C / Real.log 2) / (2 : ℝ) ^ m)
      atTop (nhds 0) := by
    have heq : (fun m : ℕ ↦
        4 * (m * m) * (C / Real.log 2) / (2 : ℝ) ^ m) =
        fun m : ℕ ↦ (4 * (C / Real.log 2)) *
          ((m : ℝ) ^ 2 / (2 : ℝ) ^ m) := by
      funext m
      push_cast
      ring
    rw [heq]
    simpa using (tendsto_nat_pow_div_two_pow 2).const_mul
      (4 * (C / Real.log 2))
  have hlogHalf : 0 < Real.log 2 / 2 := by positivity
  have evC := (tendsto_order.1 hCzero).2 _ hlogHalf
  have evM2 := (tendsto_order.1 hM2zero).2 _ hlogHalf
  have evBudget := (tendsto_order.1 hbudgetZero).2 (1 / 2 : ℝ) (by norm_num)
  have evE := (tendsto_order.1 hEZero).2 (1 : ℝ) zero_lt_one
  have evAll := (eventually_ge_atTop (max 3 (max N J))).and
    (evC.and (evM2.and (evBudget.and evE)))
  obtain ⟨M, hMlarge, hCM, hM2, hbudget, hE⟩ := evAll.exists
  refine ⟨max 3 N, M, C, le_max_left _ _, ?_, ?_, hC, ?_, ?_, hCM.le,
    hM2.le, hbudget.le, hE.le⟩
  · exact le_trans (le_max_left 3 (max N J)) hMlarge
  · exact le_trans (Nat.max_le.2 ⟨le_max_left _ _, le_trans
      (le_max_left N J) (le_max_right 3 (max N J))⟩) hMlarge
  · intro x hx
    exact hprime x (le_trans (le_max_right 3 N) hx)
  · intro j hj
    exact hmass j (le_trans (le_max_right N J)
      (le_trans (le_max_right 3 (max N J)) (hMlarge.trans hj)))

end Erdos446
