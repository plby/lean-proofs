/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos980.FinalAssembly
import ErdosProblems.Erdos980.KummerPatterns
import ErdosProblems.Erdos980.ElliottTail.UnconditionalTail

/-!
# Erdős Problem 980

For every fixed `k ≥ 2`, the sum over primes below the strict cutoff of the
least `k`-th-power nonresidue is asymptotic to a positive constant times
`x / log x`.  The total function used here agrees with Elliott's convention:
it is zero unless the prime is congruent to one modulo `k`.

The quadratic constant is also identified with Erdős's dyadic prime series.
-/

syntax (name := answerSyntax980) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

namespace Erdos980

open Filter
open scoped Asymptotics BigOperators

noncomputable section

/-- Elliott's affirmative solution of Erdős Problem 980, with the exact
strict cutoff `p < x` and the literature's totalized least-nonresidue
function. -/
theorem erdos_980 :
    answer(True) ↔ ∀ k : ℕ, 2 ≤ k → ∃ c : ℝ, 0 < c ∧
      ((fun x : ℕ ↦ ∑ p ∈ (Finset.range x).filter Nat.Prime,
          (leastKthPowerNonresidue k p : ℝ)) ~[atTop]
        (fun x : ℕ ↦ c * (x : ℝ) / Real.log (x : ℝ))) := by
  constructor
  · intro _ k hk
    obtain ⟨hc, hasymp⟩ :=
      leastKthPowerNonresidueSum_isEquivalent_of_all_primeExponentMedium
        ElliottTail.unconditionalPrimeExponentMediumEstimate k hk
    refine ⟨elliottConstant k, hc, ?_⟩
    change leastKthPowerNonresidueSum k ~[atTop]
      (fun x : ℕ ↦ elliottConstant k * (x : ℝ) / Real.log (x : ℝ))
    simpa only [erdos980Scale, mul_div_assoc] using hasymp
  · intro _
    trivial

/-- In the quadratic case, the limiting mean is Erdős's dyadic series over
the rational primes (with `rationalPrime` indexed from zero). -/
theorem erdos_980_quadratic_constant :
    elliottConstant 2 =
      ∑' j : ℕ, (rationalPrime j : ℝ) / (2 ^ (j + 1) : ℝ) :=
  elliottConstant_two_eq_dyadic

end

end Erdos980

#print axioms Erdos980.erdos_980
#print axioms Erdos980.erdos_980_quadratic_constant
