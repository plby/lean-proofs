/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBernoulliConcentration

/-! # A one-sided Bernoulli tail from an upper bound on its mean -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem FiniteLaw.independentBits_probability_count_ge_twice_budget
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ≥0) (hp : ∀ i, p i ≤ 1) (S : Finset I) (B : ℝ)
    (hmean : (∑ i ∈ S, (p i : ℝ)) ≤ B) :
    ((independentBits p hp).probability
      (fun ω ↦ 2 * B ≤ ((S.filter (fun i ↦ ω i = true)).card : ℝ)) : ℝ) ≤
      Real.exp (-B / 4) := by
  let L := independentBits p hp
  have hcover : L.probability
      (fun ω ↦ 2 * B ≤ ((S.filter (fun i ↦ ω i = true)).card : ℝ)) ≤
      L.probability (fun ω ↦ B / 2 ≤ (1 / 2 : ℝ) * centeredBernoulliSum p S ω) := by
    apply L.probability_mono
    intro ω hω
    rw [centeredBernoulliSum_eq_card_sub]
    linarith
  have hcoverR : (L.probability
      (fun ω ↦ 2 * B ≤ ((S.filter (fun i ↦ ω i = true)).card : ℝ)) : ℝ) ≤
      L.probability (fun ω ↦ B / 2 ≤ (1 / 2 : ℝ) * centeredBernoulliSum p S ω) := by
    exact_mod_cast hcover
  apply hcoverR.trans
  apply (independentBits_probability_scaled_centered_ge p hp S (1 / 2) (B / 2)
    (by norm_num)).trans
  apply Real.exp_le_exp.mpr
  nlinarith

end

end Erdos207
