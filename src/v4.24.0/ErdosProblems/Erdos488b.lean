/-

This is a Lean formalization of a solution to (the former statement
of) Erdős Problem 488.

https://www.erdosproblems.com/488

Aristotle from Harmonic found and proved the correctness of a
counterexample entirely by itself!

The counterexample is n = 13, m = 20, and A the primes up to 13.

The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

open Classical in

theorem erdos_488 :
  (∀ (A : Finset ℕ), A.Nonempty → 0 ∉ A → 1 ∉ A →
     letI B := {n ≥ 1 | ∀ a ∈ A, ¬ a ∣ n}
     ∀ᵉ (n : ℕ) (m > n), A.max ≤ n →
       ((Finset.Icc 1 m).filter (· ∈ B)).card / (m : ℚ) <
         2 * ((Finset.Icc 1 n).filter (· ∈ B)).card / n) ↔ False :=
by
  constructor;
  · contrapose!;
    rintro -;
    -- Let's choose A = {2, 3, 5, 7, 11, 13}.
    use {2, 3, 5, 7, 11, 13};
    refine' ⟨ _, _, _, 13, 200, _, _, _ ⟩ <;> norm_cast;
    with_unfolding_all eq_refl
  · tauto
