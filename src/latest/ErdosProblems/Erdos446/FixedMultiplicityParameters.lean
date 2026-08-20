/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.DyadicParameters

/-!
# Erdős Problem 446: parameters for prescribed multiplicity

The fixed-multiplicity argument uses the same prime-block estimates as the
ordinary lower bound, but needs a smaller close-pair error and must absorb a
fixed prefix-energy cutoff.  All relevant errors are a fixed polynomial in
`M` divided by `2^M`; this file chooses one `M` for all of them.
-/

namespace Erdos446

open Filter Real
open scoped Topology

noncomputable def fixedMultiplicityEnergyConstant : ℝ :=
  8000 * Real.exp 4

noncomputable def fixedMultiplicityEnergyCutoff : ℝ :=
  2 * fixedMultiplicityEnergyConstant

theorem fixedMultiplicityEnergyConstant_pos :
    0 < fixedMultiplicityEnergyConstant := by
  dsimp [fixedMultiplicityEnergyConstant]
  positivity

theorem fixedMultiplicityEnergyCutoff_pos :
    0 < fixedMultiplicityEnergyCutoff := by
  exact mul_pos (by norm_num) fixedMultiplicityEnergyConstant_pos

/-- One parameter package simultaneously supplies the block PNT, the sharp
block-mass error, the selection condition, and the numerical quality bound
used by the size-truncated fixed-multiplicity family. -/
theorem exists_fixedMultiplicity_parameters :
    ∃ N M : ℕ, ∃ C E Q D : ℝ,
      3 ≤ N ∧ 3 ≤ M ∧ N ≤ M ∧ 0 < C ∧ 0 < D ∧
      (∀ x : ℕ, N ≤ x →
        (1 / 4 : ℝ) / Real.log (x : ℝ) ≤ dyadicPrimeMass x ∧
        dyadicPrimeMass x ≤ 3 / Real.log (x : ℝ)) ∧
      (∀ j : ℕ, M ≤ j →
        |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j) ∧
      C / (2 : ℝ) ^ M ≤ Real.log 2 / 2 ∧
      2 * (M : ℝ) ^ 2 / (2 : ℝ) ^ M ≤ Real.log 2 / 2 ∧
      (4 * (M * M) * C + 12 * (M * M) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ M) ≤ 1 / 100 ∧
      4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ E ∧
      0 ≤ Q ∧
      Real.exp E * (1 + Q * (2 * D)) ≤ 13 / 10 ∧
      Q = 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M) ∧
      D = fixedMultiplicityEnergyConstant := by
  obtain ⟨N₀, M₀, C, hN₀, hM₀, hNM₀, hC, hprime, hmass,
      hCM₀, hsmall₀, hbudget₀, hE₀⟩ := exists_ford_fixed_parameters
  let D : ℝ := fixedMultiplicityEnergyConstant
  let E : ℝ := Real.log (11 / 10 : ℝ)
  have hD : 0 < D := by
    dsimp [D]
    exact fixedMultiplicityEnergyConstant_pos
  have hE : 0 < E := by
    dsimp [E]
    exact Real.log_pos (by norm_num)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow : Tendsto (fun m : ℕ ↦ (2 : ℝ) ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hCzero : Tendsto (fun m : ℕ ↦ C / (2 : ℝ) ^ m)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hpow.inv_tendsto_atTop.const_mul C
  have hM2zero : Tendsto
      (fun m : ℕ ↦ 2 * (m : ℝ) ^ 2 / (2 : ℝ) ^ m)
      atTop (nhds 0) := by
    simpa [mul_div_assoc] using
      (tendsto_nat_pow_div_two_pow 2).const_mul 2
  have hbudgetZero : Tendsto
      (fun m : ℕ ↦
        (4 * (m * m) * C + 12 * (m * m) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ m)) atTop (nhds 0) := by
    have hlogne : Real.log 2 ≠ 0 := hlog.ne'
    have heq : (fun m : ℕ ↦
        (4 * (m * m) * C + 12 * (m * m) ^ 2) /
          (Real.log 2 * (2 : ℝ) ^ m)) =
        fun m : ℕ ↦
          (4 * C / Real.log 2) * ((m : ℝ) ^ 2 / (2 : ℝ) ^ m) +
          (12 / Real.log 2) * ((m : ℝ) ^ 4 / (2 : ℝ) ^ m) := by
      funext m
      push_cast
      rw [show ((m : ℝ) * m) ^ 2 = (m : ℝ) ^ 4 by ring]
      field_simp [hlogne]
    rw [heq]
    simpa using
      ((tendsto_nat_pow_div_two_pow 2).const_mul (4 * C / Real.log 2)).add
        ((tendsto_nat_pow_div_two_pow 4).const_mul (12 / Real.log 2))
  have hEZero : Tendsto
      (fun m : ℕ ↦ 4 * (m * m) * (C / Real.log 2) /
        (2 : ℝ) ^ m) atTop (nhds 0) := by
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
  have hQZero : Tendsto
      (fun m : ℕ ↦
        (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ m)) * (2 * D))
      atTop (nhds 0) := by
    have hlogSq : Real.log 2 ^ 2 ≠ 0 := pow_ne_zero 2 hlog.ne'
    have heq : (fun m : ℕ ↦
        (56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ m)) * (2 * D)) =
        fun m : ℕ ↦ (112 * D / Real.log 2 ^ 2) *
          (1 / (2 : ℝ) ^ m) := by
      funext m
      field_simp [hlogSq]
      ring
    rw [heq]
    simpa [one_div] using hpow.inv_tendsto_atTop.const_mul
      (112 * D / Real.log 2 ^ 2)
  have evC := (tendsto_order.1 hCzero).2 _ (by positivity :
    0 < Real.log 2 / 2)
  have evM2 := (tendsto_order.1 hM2zero).2 _ (by positivity :
    0 < Real.log 2 / 2)
  have evBudget := (tendsto_order.1 hbudgetZero).2 (1 / 100 : ℝ)
    (by norm_num)
  have evE := (tendsto_order.1 hEZero).2 E hE
  have evQ := (tendsto_order.1 hQZero).2 (1 / 10 : ℝ) (by norm_num)
  have evAll := (eventually_ge_atTop (max 3 M₀)).and
    (evC.and (evM2.and (evBudget.and (evE.and evQ))))
  obtain ⟨M, hMlarge, hCM, hsmall, hbudget, hErr, hQsmall⟩ := evAll.exists
  let Q : ℝ := 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)
  have hM : 3 ≤ M := (le_max_left 3 M₀).trans hMlarge
  have hM₀M : M₀ ≤ M := (le_max_right 3 M₀).trans hMlarge
  have hNM : N₀ ≤ M := hNM₀.trans hM₀M
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hquality : Real.exp E * (1 + Q * (2 * D)) ≤ 13 / 10 := by
    have hexp : Real.exp E = (11 / 10 : ℝ) := by
      dsimp [E]
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 11 / 10)]
    rw [hexp]
    dsimp [Q] at hQsmall ⊢
    nlinarith
  refine ⟨N₀, M, C, E, Q, D, hN₀, hM, hNM, hC, hD, hprime,
    ?_, hCM.le, hsmall.le, hbudget.le, hErr.le, hQ, hquality, rfl, rfl⟩
  intro j hj
  exact hmass j (hM₀M.trans hj)

end Erdos446
