/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1140.
https://www.erdosproblems.com/forum/thread/1140

Informal authors:
- Mihai Epure
- Alexandru Gica
- Richard A. Mollin
- Hugh C. Williams

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1140.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-5.4 Pro
-/
import ErdosProblems.Erdos1140.Erdos1140Analytic

/-!
# Erdős Problem 1140

For a positive natural number `n`, every positive value `n - 2*x^2` is
required to be prime.  This file proves that only finitely many `n` have
that property, answering Erdős Problem 1140 in the negative.

The exact predicate and elementary finiteness reduction are in
`ErdosProblems.Erdos1140.Erdos1140Base`.  The axiom-clean Burgess, quadratic-zeta, and
Siegel argument supplying a small congruence prime is in
`ErdosProblems.Erdos1140.Erdos1140Analytic`.
-/

namespace Erdos1140

/-- **Resolution of Erdős Problem 1140.**  There are only finitely many
positive natural numbers `n` for which every positive value `n - 2*x^2` is
prime. -/
theorem not_erdos_1140 : Set.Finite {n : ℕ | Good n} :=
  finite_good_of_eventually_small_solvable_prime
    eventually_small_solvable_prime

end Erdos1140

#print axioms Erdos1140.not_erdos_1140

alias _root_.Erdos1140.erdos_1140 := _root_.Erdos1140.not_erdos_1140
