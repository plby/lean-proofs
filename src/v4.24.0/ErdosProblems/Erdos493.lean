/-

This is a Lean formalization of a solution to Erdős Problem 493.
https://www.erdosproblems.com/493

This proof was written by Aristotle.  It found the proof given only
the formal statement.

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

namespace Erdos493

/--
There exists a `k` such that every sufficiently large integer `n`
can be written as `∏ aᵢ - ∑ aᵢ` with all `aᵢ ≥ 2`.
-/
theorem erdos_493 :
  ∃ k : ℕ, ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
    ∃ a : Fin k → ℤ,
      (∀ i : Fin k, (2 : ℤ) ≤ a i) ∧
      (∏ i : Fin k, a i) - (∑ i : Fin k, a i) = n := by
  use 2;
  use 0;
  -- For any non-negative integer $n$, we can choose $a_0 = n + 2$ and $a_1 = 2$.
  intro n hn
  use ![n + 2, 2];
  norm_num [ Fin.forall_fin_two ];
  exact ⟨ hn, by ring ⟩
