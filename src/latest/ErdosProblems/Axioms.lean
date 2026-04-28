import Mathlib

open Nat Finset Real Filter Asymptotics

noncomputable abbrev nth_prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

axiom nth_prime_asymp :
    (fun n ↦ ((nth_prime n) : ℝ)) ~[atTop] (fun n ↦ (n : ℝ) * Real.log (n : ℝ))

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
