/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import Mathlib

open Nat Finset Real Filter Asymptotics

noncomputable abbrev nth_prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

axiom nth_prime_asymp :
    (fun n ↦ ((nth_prime n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) * Real.log (n : ℝ))

/-! ## Axioms from unit fractions -/

/-- **Bloom–Mehta formalized statement (Theorem 3).**
This is the statement at line 2042 of
`https://github.com/b-mehta/unit-fractions/blob/master/src/final_results.lean`,
translated from Lean 3 / mathlib3 into Lean 4 / Mathlib4.

The Bloom–Mehta formalization is in Lean 3, and there is currently no
automated way to import Lean 3 projects into a Lean 4 build.
Consequently we state this theorem here with `axiom` as a trusted
external result. Should a Lean 4 port of the `unit-fractions`
repository become available, this `axiom` can be replaced by `theorem`
proved by an import. -/
axiom unit_fractions_upper_log_density :
    ∃ C : ℝ, ∀ᶠ (N : ℕ) in atTop, ∀ A ⊆ Icc 1 N,
      C * (Real.log (Real.log (Real.log N)) /
        Real.log (Real.log N)) * Real.log N
        ≤ ∑ n ∈ A, (1 : ℝ) / n →
      ∃ S ⊆ A, ∑ n ∈ S, (1 / n : ℚ) = 1

/-- A set `B` of integers is *admissible* if for every prime `p`, the
residues of `B` modulo `p` do not cover all of `ZMod p`. -/
def Admissible (B : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (Finset.image (· % (p : ℤ)) B).card < p

/-! ## Axioms from analytic number theory -/

/-- **Maynard–Tao Theorem** (2015). For any `m ≥ 2`, if `B` is an
admissible set with `|B| log |B| > e^{8m+4}`, then there are infinitely
many `n` such that at least `m` of `{n + b : b ∈ B}` are prime. -/
axiom maynard_tao (m : ℕ) (hm : 2 ≤ m) (B : Finset ℤ)
    (hB : Admissible B) (hk : exp (8 * m + 4) < B.card * Real.log B.card) :
    ∀ N : ℕ, ∃ n : ℤ, N < n ∧
      m ≤ (B.filter (fun b ↦ (n + b).natAbs.Prime)).card

/-- **Mertens' third theorem** (1874). For `n ≥ 3`, the product
`∏_{p prime, p ≤ n} (1 - 1/p) ≥ 1/(3 log n)`. -/
axiom mertens_third_theorem (n : ℕ) (hn : 3 ≤ n) :
    1 / (3 * Real.log n) ≤
      ∏ p ∈ (Finset.range (n + 1)).filter Prime, (1 - 1 / (p : ℝ))

/-- **Tao–Teräväinen theorem** (Theorem 1.1 of Tao–Teräväinen, 2025).

This is a deep theorem from analytic number theory and is stated here
without proof. It shows `ω (N + k) ≤ Ω(N + k) ≤ C·k` for some absolute
constant `C > 0` and infinitely many `N`. -/
axiom tao_teravainen : ∃ C : ℝ, 0 < C ∧
    (∃ᶠ N in atTop, ∀ k : ℕ, 0 < k →
      (N + k).factorization.support.card ≤
          (N + k).factorization.sum (fun _ k => k) ∧
        (N + k).factorization.sum (fun _ k => k) ≤ C * k)

/-! ## Axioms from cototient theory -/

/-- **Browkin-Schinzel noncototient theorem.** For every `k ≥ 1`,
`2^k * 509203` is not of the form `n - phi(n)`. -/
axiom browkin_schinzel_noncototient (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∃ n : ℕ, 2 ^ k * 509203 = n - n.totient
