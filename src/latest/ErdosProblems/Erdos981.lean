/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 981.
https://www.erdosproblems.com/forum/thread/981

Informal authors:
- P. D. T. A. Elliott

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos981.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos981.Final

/-!
# Erdős Problem 981

For an odd prime `p`, let `eventualThreshold ε p` be the least positive
integer `m` such that every quadratic-character partial sum from time `m`
onward is strictly smaller than `ε N`. Elliott's theorem says that, for
every `ε > 0`, the sum of these thresholds over primes below `x` is
asymptotic to a positive constant times `x / log x`.
-/

open Filter
open scoped Asymptotics

namespace Erdos981

/-- Elliott's resolution of Erdős Problem 981, in the exact eventual-time
formulation. -/
theorem erdos_981 {ε : ℝ} (hε : 0 < ε) :
    ∃ cε : ℝ, 0 < cε ∧
      thresholdPrimeSum ε ~[atTop]
        (fun x : ℕ => cε * ((x : ℝ) / Real.log (x : ℝ))) :=
  test_erdos_981 hε

end Erdos981

#print axioms Erdos981.erdos_981
