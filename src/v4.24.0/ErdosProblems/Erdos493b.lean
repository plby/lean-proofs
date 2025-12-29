/-

This is a Lean formalization of a solution to Erdős Problem 493.
https://www.erdosproblems.com/493

This proof was written by ChatGPT.  It found the proof given only the
formal statement.

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

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
  -- Take `k = 2` and `N = 0`.
  refine ⟨2, 0, ?_⟩
  intro n hn
  -- Choose a₀ = 2 and a₁ = n + 2.
  let a : Fin 2 → ℤ := fun i => if (i : ℕ) = 0 then 2 else n + 2
  refine ⟨a, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [a]
    linarith [hn]
  · -- Compute `∏ aᵢ - ∑ aᵢ` on `Fin 2`.
    simp [a, Fin.prod_univ_two, Fin.sum_univ_two]
    ring
