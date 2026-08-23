/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 248.
https://www.erdosproblems.com/forum/thread/248

Informal authors:
- Terence Tao
- Joni Teräväinen

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos248.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/248.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos248.TailAssembly

/-!
# Erdős Problem 248

There is an absolute constant `C > 0` and infinitely many natural numbers
`n` such that, simultaneously for every positive shift `k`, the number of
distinct prime factors of `n + k` is at most `C k`.

The detailed mathematical proof and the Leanization map are in `tex/248.tex`.
The imported development implements the Tao--Teräväinen weighted-sieve
argument directly for `ω`.
-/

open scoped ArithmeticFunction.omega

namespace Erdos248

/-- Affirmative resolution of Erdős Problem 248. -/
theorem erdos_248 :
    ∃ C > (0 : ℝ),
      {n : ℕ | ∀ k ≥ 1, ω (n + k) ≤ C * k}.Infinite :=
  erdos248_resolved

#print axioms Erdos248.erdos_248

end Erdos248
