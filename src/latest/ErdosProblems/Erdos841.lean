/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos841.LowerBound

/-!
# Erdős Problem 841

This is the public entry point for the complete formal resolution.  The core
combinatorial, distributional, and many-small-values development is in
`Erdos841.Core`; the unconditional simultaneous-Pell height argument and its
asymptotic inversion are in `Erdos841.LowerBound`.
-/

namespace Erdos841

noncomputable section

/-- The complete formal resolution of Erdős Problem 841: the exact
large-prime branch, the complementary square-root estimate, the BPZ
distribution theorem, the `x^(1-o(1))` family of small values, and the
unconditional pointwise lower bound. -/
theorem erdos841_final_resolution :
    (∀ n : ℕ, 1 < n →
      Real.sqrt (2 * (n : ℝ)) + 1 < (largestPrimeFactor n : ℝ) →
        t n = largestPrimeFactor n) ∧
    (∀ n : ℕ,
      (largestPrimeFactor n : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) + 1 →
        (t n : ℝ) ≤ 40 * Real.sqrt (n : ℝ)) ∧
    (∀ c : ℝ, 0 < c → c ≤ 1 →
      Filter.Tendsto
        (fun x : ℕ ↦
          (((movingSmallTUpTo x c).card : ℝ) -
            ((movingSmoothUpTo x c).card : ℝ)) / (x : ℝ))
        Filter.atTop (nhds 0)) ∧
    (Filter.Tendsto
        (fun x : ℕ ↦ Real.log ((manySmallUpTo x).card : ℝ) /
          Real.log (x : ℝ))
        Filter.atTop (nhds 1) ∧
      ∀ x n : ℕ, n ∈ manySmallUpTo x ↔
        1 ≤ n ∧ n ≤ x ∧
          (t n : ℝ) ≤ Real.exp
            (20 * Real.sqrt (Real.log n * Real.log (Real.log n)))) ∧
    (∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n →
      pellLowerBoundConstant *
          (Real.log (Real.log (n : ℝ)) ^ ((6 : ℝ) / 5) *
            Real.log (Real.log (Real.log (n : ℝ))) ^ (-((1 : ℝ) / 5))) ≤
        (t n : ℝ)) :=
  erdos841_complete_resolution

/-- The same complete resolution with its positive lower-bound constant
existentially quantified, so the statement does not expose construction-level
height estimates. -/
theorem erdos841_comparator_resolution :
    (∀ n : ℕ, 1 < n →
      Real.sqrt (2 * (n : ℝ)) + 1 < (largestPrimeFactor n : ℝ) →
        t n = largestPrimeFactor n) ∧
    (∀ n : ℕ,
      (largestPrimeFactor n : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) + 1 →
        (t n : ℝ) ≤ 40 * Real.sqrt (n : ℝ)) ∧
    (∀ c : ℝ, 0 < c → c ≤ 1 →
      Filter.Tendsto
        (fun x : ℕ ↦
          (((movingSmallTUpTo x c).card : ℝ) -
            ((movingSmoothUpTo x c).card : ℝ)) / (x : ℝ))
        Filter.atTop (nhds 0)) ∧
    (Filter.Tendsto
        (fun x : ℕ ↦ Real.log ((manySmallUpTo x).card : ℝ) /
          Real.log (x : ℝ))
        Filter.atTop (nhds 1) ∧
      ∀ x n : ℕ, n ∈ manySmallUpTo x ↔
        1 ≤ n ∧ n ≤ x ∧
          (t n : ℝ) ≤ Real.exp
            (20 * Real.sqrt (Real.log n * Real.log (Real.log n)))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop, ¬IsSquare n →
      C *
          (Real.log (Real.log (n : ℝ)) ^ ((6 : ℝ) / 5) *
            Real.log (Real.log (Real.log (n : ℝ))) ^ (-((1 : ℝ) / 5))) ≤
        (t n : ℝ)) := by
  obtain ⟨hlarge, hsmall, hdistribution, hmany, hlower⟩ :=
    erdos841_final_resolution
  exact ⟨hlarge, hsmall, hdistribution, hmany,
    pellLowerBoundConstant, pellLowerBoundConstant_pos, hlower⟩

end

end Erdos841

#print axioms Erdos841.erdos841_final_resolution
#print axioms Erdos841.erdos841_comparator_resolution
#print axioms Erdos841.erdos841_lower_bound_explicit
#print axioms Erdos841.erdos841_distributional_resolution
#print axioms Erdos841.erdos841_many_small_values_global
#print axioms Erdos841.erdos841_selfridge_sqrt_bound_all
