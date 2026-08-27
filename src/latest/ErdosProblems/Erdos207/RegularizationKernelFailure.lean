/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationKernel
import ErdosProblems.Erdos207.FiniteKernelFailureBound

/-! # Failure probability for the actual adaptive regularization kernel -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem regularizationKernel_failure_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (b t : ℕ) (S : HypergraphRegularizationState V k) :
    ((regularizationKernel G0 H0 hGH hk hsize b t S).probability (fun S' ↦ S'.2 = true) : ℝ) ≤
      (if S.2 = true then 1 else 0) + 2 * Fintype.card V * Real.exp (-(b : ℝ) / 8192) := by
  classical
  have heps : (0 : ℝ) ≤ 2 * Fintype.card V * Real.exp (-(b : ℝ) / 8192) := by positivity
  by_cases hA : RegularizationActive G0 H0 b t S
  · simp only [hA.1, Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [regularizationKernel_active G0 H0 hGH hk hsize b t S hA, FiniteLaw.probability_map]
    simp_rw [regularizationBatchOutcome_failed_iff]
    apply (hypergraphRegularizationParameters_failure_probability
      (regularizationCurrentFamily G0 S) (regularizationCurrentFamily H0 S)
      (regularizationCurrentFamily_mono_base hGH S) hk
      (Nat.zero_lt_of_lt hA.2.1) hsize hA.2.2.2).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hb : (b : ℝ) ≤ finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) := by
      exact_mod_cast (Nat.le_of_lt hA.2.1)
    linarith
  · rw [regularizationKernel_inactive G0 H0 hGH hk hsize b t S hA, FiniteLaw.probability_pure]
    by_cases hf : S.2 = true <;> simp [hf, heps]

theorem regularizationEvolve_failure_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (b t : ℕ) :
    ((FiniteLaw.evolveKernels (regularizationKernel G0 H0 hGH hk hsize b) t
      (FiniteLaw.pure (regularizationInitialState V k))).probability (fun S ↦ S.2 = true) : ℝ) ≤
      t * (2 * Fintype.card V * Real.exp (-(b : ℝ) / 8192)) := by
  exact FiniteLaw.probability_evolve_failure_le
    (regularizationKernel G0 H0 hGH hk hsize b)
    (fun S : HypergraphRegularizationState V k ↦ S.2 = true)
    (2 * Fintype.card V * Real.exp (-(b : ℝ) / 8192))
    (fun i S ↦ regularizationKernel_failure_le G0 H0 hGH hk hsize b i S)
    (regularizationInitialState V k) (by simp [regularizationInitialState]) t

end

end Erdos207
