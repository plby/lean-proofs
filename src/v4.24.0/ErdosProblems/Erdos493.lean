/-

This is a Lean formalization of a solution to Erdős Problem 493.
https://www.erdosproblems.com/493


Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

-/

import Mathlib

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
