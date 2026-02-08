/-

This is a Lean solution to a MISFORMALIZATION of Erdős Problem 480.
https://www.erdosproblems.com/480

The statement is from the Formal Conjectures project at
https://github.com/google-deepmind/formal-conjectures/blob/f33f5ddb49f6077e34025917965bcd1bbd920d73/FormalConjectures/ErdosProblems/480.lean#L27-L37

The proof was found by Aristotle from Harmonic.

The issue is that the statement assumes m ≠ 0 but probably meant n ≠
0, so the proof exploits n = 0 in a trivial way.

The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

namespace Erdos480x

theorem misformalized_erdos_480 :
  (∀ (x : ℕ → ℝ), (∀ n, x n ∈ Set.Icc 0 1) →
    {(m, n) | (m) (n) (_ : m ≠ 0) (_ : |x (m + n) - x m| ≤ 1 / (√5 * n))}.Infinite) := by
  -- Let's choose any $x \in \ell^\infty$.
  intro x hx;
  refine Set.infinite_of_injective_forall_mem ( fun m n hmn => by aesop ) fun m => ⟨ m + 1, 0, ?_, ?_, rfl ⟩ <;> norm_num
