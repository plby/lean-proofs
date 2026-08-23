/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 534.
https://www.erdosproblems.com/forum/thread/534

Informal authors:
- Rudolf Ahlswede
- Levon H. Khachatrian

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos534.md
-/
import ErdosProblems.Erdos534.Erdos534Assembly

/-!
# Erdős Problem 534

Ahlswede and Khachatrian proved that, if the distinct prime factors of
`N` are `q₁ < ⋯ < qᵣ`, a largest subset of `{1, …, N}` containing `N`
whose distinct elements have gcd greater than one is obtained, for some
`j`, by taking all multiples in the interval of one of

`2q₁, …, 2qⱼ, q₁⋯qⱼ`.

The imported development proves the compression theorem, the pull-fiber
sieve estimate (including its finite prime-counting certificate), and the
terminal classification.  The theorem below states the result directly in
terms of `N.primeFactors`, without assuming a separately supplied
factorization.
-/

namespace Erdos534

/-- **Resolution of Erdős Problem 534 (Ahlswede--Khachatrian).** -/
theorem erdos_534 (N : ℕ) (hN : 2 ≤ N) :
    ∃ q ∈ N.primeFactors,
      Admissible N (candidate N q) ∧
        ∀ A, Admissible N A → A.card ≤ (candidate N q).card :=
  erdos_534_aux N hN

end Erdos534

#print axioms Erdos534.erdos_534
