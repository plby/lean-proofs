/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 823.
https://www.erdosproblems.com/forum/thread/823

Informal authors:
- Paul Pollack

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos823.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos823.Assembly
import ErdosProblems.Erdos823.AffineSieveS2

/-!
# Erdős Problem 823

Pollack proved that every real `α ≥ 1` is a limit of quotients `n / m` of
positive integers having the same sum of divisors.  The analytic input is the
unconditional unequal-slope Maynard theorem proved in `AffineSieveS2`; the
elementary coprime-product construction is in `Assembly`.

The detailed mathematical reconstruction and Leanization map are in
`tex/823.tex`.
-/

syntax (name := answerSyntax823) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

namespace Erdos823

open Filter Topology
open scoped ArithmeticFunction.sigma

/-- Pollack's affirmative result in a form without the `answer` wrapper. -/
theorem exists_equal_sigma_sequences {α : ℝ} (hα : 1 ≤ α) :
    ∃ n m : ℕ → ℕ,
      (∀ k, 0 < n k) ∧
      (∀ k, 0 < m k) ∧
      (∀ k, σ 1 (n k) = σ 1 (m k)) ∧
      Tendsto (fun k ↦ (n k : ℝ) / (m k : ℝ)) atTop (nhds α) := by
  have hε : ∀ k : ℕ, (0 : ℝ) < 1 / (k + 1 : ℕ) := by
    intro k
    positivity
  choose n m hn hm hσ happ using fun k : ℕ ↦
    sigma_quotient_approx_of_affine
      AffineSieve.affinePrimePairProperty_105 hα (hε k)
  refine ⟨n, m, hn, hm, hσ, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hεpos
  have hevent : ∀ᶠ k : ℕ in atTop, (1 : ℝ) / (k + 1 : ℕ) < ε := by
    have hlim : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_order.1 hlim).2 ε hεpos
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨N, fun k hk ↦ ?_⟩
  rw [Real.dist_eq]
  exact (happ k).trans (hN k hk)

/-- **Erdős Problem 823 (Pollack).**  For every `α ≥ 1`, there are positive
integer sequences whose quotients tend to `α` and whose divisor sums agree
term by term. -/
theorem erdos_823 : answer(True) ↔
    ∀ α : ℝ, 1 ≤ α →
      ∃ n m : ℕ → ℕ,
        (∀ k, 0 < n k) ∧
        (∀ k, 0 < m k) ∧
        (∀ k, σ 1 (n k) = σ 1 (m k)) ∧
        Tendsto (fun k ↦ (n k : ℝ) / (m k : ℝ)) atTop (nhds α) := by
  constructor
  · intro _ α hα
    exact exists_equal_sigma_sequences hα
  · intro _
    trivial

#print axioms Erdos823.erdos_823

end Erdos823
