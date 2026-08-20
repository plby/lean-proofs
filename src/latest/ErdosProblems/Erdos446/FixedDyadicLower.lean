/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.DyadicParameters

/-!
# Erdős Problem 446: the uniform finite lower construction

This file freezes the finitely many analytic parameters in Ford's lower
construction.  The only remaining parameters are the depth `K` and an
ambient endpoint lying beyond the size scale required by that depth.
-/

namespace Erdos446

theorem exists_uniform_ford_sized_dyadic_lower :
    ∃ N M : ℕ, ∃ C : ℝ,
      3 ≤ N ∧ 3 ≤ M ∧ N ≤ M ∧ 0 < C ∧
      ∀ K y : ℕ, 0 < K → fordConstructionScale M K ≤ y →
        smallPrimeEulerDensity (2 * y) *
            (((1 / 96 : ℝ) / Real.log (y : ℝ)) *
              ((((2 * Real.log 2 : ℝ) ^ K / 2) ^ 2 /
                ((2 * Real.log 2 : ℝ) ^ K * Real.exp 1 *
                  (2 + 56 /
                    (Real.log 2 ^ 2 * (2 : ℝ) ^ M)))) *
                ((1 / 2 : ℝ) *
                  ((K : ℝ) ^ (K - 1) / (K.factorial : ℝ))))) ≤
          epsilon y (2 * y) := by
  obtain ⟨N, M, C, hN, hM, hNM, hC, hprime, hmass, hCM, hsmall,
    hbudget, hE⟩ := exists_ford_fixed_parameters
  refine ⟨N, M, C, hN, hM, hNM, hC, ?_⟩
  intro K y hK hscale
  have hMB : M ≤ fordConstructionBound M K :=
    fordConstructionBound_ge_M hK
  have hNB : N ≤ fordConstructionBound M K := hNM.trans hMB
  have hendpoint : ∀ i : Fin K, N ≤ blockEndpoint (M + i) := by
    intro i
    exact hNM.trans ((Nat.le_add_right M i).trans
      (blockEndpoint_ge_index (M + i)))
  have hmass' : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val) := by
    intro i
    exact hmass (M + i) (by omega)
  have hhalf : ∀ i : Fin K,
      Real.log 2 / 2 ≤ primeBlockMass (M + i) := by
    intro i
    have hi := hmass' i
    have hpow : (2 : ℝ) ^ M ≤ (2 : ℝ) ^ (M + i.val) := by
      rw [pow_add]
      exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
    have hCi : C / (2 : ℝ) ^ (M + i.val) ≤ C / (2 : ℝ) ^ M := by
      exact div_le_div_of_nonneg_left hC.le (by positivity) hpow
    have hlower := (abs_le.mp hi).1
    linarith
  have hselect : ∀ b ∈ cappedCompositions M K, ∀ i : Fin K,
      (b i : ℝ) * (1 / (blockEndpoint (M + i) : ℝ)) ≤
        primeBlockMass (M + i) :=
    capped_selection_condition (by omega) hsmall hhalf
  exact ford_sized_dyadic_lower_core hM hK hC.le hN hNB hscale
    hendpoint hprime hmass' hselect hbudget hhalf hE

end Erdos446
