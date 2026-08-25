/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos13.Erdos13Kneser
import Util.FranklRodl
import Util.MertensProduct
import Util.MaynardBFT.Result
import Util.Linnik.Theorem

open Nat Finset Real Filter Asymptotics Topology
open scoped Pointwise

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

/-- The Maynard–Tao theorem (Banks–Freiberg–Turnage-Butterbaugh corollary): for every
`m ≥ 1`, there exists `Cₘ ≥ 1` such that for every coprime residue class `a mod q`
(with `q ≥ 1`), there are infinitely many index-runs of `m` consecutive primes in
that class with total gap `≤ q · Cₘ`. -/
theorem maynardTaoBFT :
  ∀ m : ℕ, 0 < m → ∃ C : ℕ, 0 < C ∧ ∀ q : ℕ, 0 < q → ∀ a : ℤ,
    Int.gcd a (q : ℤ) = 1 →
    ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧
      (∀ j, j < m → (Nat.nth Nat.Prime (r + j) : ℤ) ≡ a [ZMOD (q : ℤ)]) ∧
      Nat.nth Nat.Prime (r + m - 1) - Nat.nth Nat.Prime r ≤ q * C :=
  MaynardBFT.consecutive_primes

/-- **Tao–Teräväinen theorem** (Theorem 1.1 of Tao–Teräväinen, 2025).

This is a deep theorem from analytic number theory and is stated here
without proof. It shows `ω (N + k) ≤ Ω(N + k) ≤ C·k` for some absolute
constant `C > 0` and infinitely many `N`. -/
axiom tao_teravainen : ∃ C : ℝ, 0 < C ∧
    (∃ᶠ N in atTop, ∀ k : ℕ, 0 < k →
      (N + k).factorization.support.card ≤
          (N + k).factorization.sum (fun _ k => k) ∧
        (N + k).factorization.sum (fun _ k => k) ≤ C * k)

/-- An (integral) binary quadratic form `f(X,Y) = a X^2 + b X Y + c Y^2`. -/
structure BinQuadForm where
  a : ℤ
  b : ℤ
  c : ℤ

namespace BinQuadForm

/-- Evaluate the form on integer inputs. -/
def eval (f : BinQuadForm) (x y : ℤ) : ℤ :=
  f.a * x * x + f.b * x * y + f.c * y * y

/-- Discriminant `Δ = b^2 - 4ac`. -/
def discr (f : BinQuadForm) : ℤ :=
  f.b * f.b - 4 * f.a * f.c

/-- `f` is primitive if `gcd(a,b,c) = 1`. -/
def Primitive (f : BinQuadForm) : Prop :=
  Int.gcd f.a (Int.gcd f.b f.c) = 1

/--
A convenient (sufficient) positive-definiteness condition for integral binary quadratic forms:
`a > 0` and discriminant is negative.
(For integer forms this is equivalent to positive definiteness over `ℝ`.)
-/
def PosDef (f : BinQuadForm) : Prop :=
  0 < f.a ∧ f.discr < 0

/--
Counting function `B_f(x)`: number of *natural numbers* `n ≤ x` represented by `f`.
(Here “represented” means `∃ u v : ℤ, f(u,v) = n`.)
-/
noncomputable def B (f : BinQuadForm) (x : ℝ) : ℕ :=
  Nat.card {n : ℕ | (n : ℝ) ≤ x ∧ ∃ u v : ℤ, f.eval u v = (n : ℤ)}

end BinQuadForm

/--
**Bernays' theorem.**

Let `f(X,Y)=aX^2+bXY+cY^2` be a primitive positive definite binary quadratic form
with non-square discriminant `Δ`. Then there exists a constant `C_Δ > 0` such that
`B_f(x) ~ C_Δ * x / sqrt(log x)` as `x → ∞`.

We phrase this so that `C_Δ` depends only on `Δ` (and works for every `f` of that discriminant).
-/
axiom bernays
    (Δ : ℤ) (hΔnonsq : ¬ ∃ z : ℤ, z * z = Δ) :
    ∃ CΔ : ℝ, 0 < CΔ ∧
      ∀ f : BinQuadForm,
        f.Primitive →
        f.PosDef →
        f.discr = Δ →
        (fun x : ℝ => (f.B x : ℝ))
          ~[Filter.atTop]
          (fun x : ℝ => CΔ * x / Real.sqrt (Real.log x))

/-- **Dusart's Mertens product estimate** (Theorem 5.1): for `x ≥ 2278382`,
`|∏_{p≤x}(1-1/p) - 1/(e^γ log x)| ≤ 1/(5 e^γ log⁴ x)`. -/
axiom dusart_mertens_product (x : ℝ) (hx : x ≥ 2278382) :
    |∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
        (1 - 1 / (p : ℝ)) -
      1 / (Real.exp Real.eulerMascheroniConstant * Real.log x)| ≤
      1 / (5 * Real.exp Real.eulerMascheroniConstant * Real.log x ^ 4)

/-- **Dusart's prime-counting lower estimate** (Theorem 5.2): for `x ≥ 88789`,
`π(x) ≥ x/log x + x/log² x + 2x/log³ x`. -/
axiom dusart_pi_lower (x : ℝ) (hx : x ≥ 88789) :
    x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 ≤
      (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ)

/-- **Dusart's prime-counting upper estimate** (Theorem 5.2): for `x > 1`,
`π(x) ≤ x/log x + x/log² x + 2.53816x/log³ x`. -/
axiom dusart_pi_upper (x : ℝ) (hx : x > 1) :
    (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) ≤
      x / Real.log x + x / Real.log x ^ 2 + 2.53816 * x / Real.log x ^ 3

/-- **Dusart's Chebyshev estimate** (Theorem 5.3): for `x ≥ 2`,
`|ψ(x) - x| < 1.66x/log² x`. -/
axiom dusart_chebyshev (x : ℝ) (hx : x ≥ 2) :
    |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), ArithmeticFunction.vonMangoldt n) - x| <
      1.66 * x / Real.log x ^ 2

/-- **Shiu's theorem** (2000): for any positive length `l`, any modulus
`q ≥ 1`, and any `a` coprime to `q`, there are arbitrarily late runs of `l`
consecutive primes each congruent to `a` modulo `q`.

D. K. L. Shiu, "Strings of Congruent Primes",
J. London Math. Soc. 61 (2000), 359-373.
This form follows from the unconditional `maynardTaoBFT` theorem. -/
theorem shiu_consecutive_primes
    (l : ℕ) (hl : 1 ≤ l) (a q : ℕ) (hq : 1 ≤ q) (haq : Nat.Coprime a q) (N : ℕ) :
    ∃ m, N ≤ m ∧ ∀ i, i < l → Nat.nth Nat.Prime (m + i) ≡ a [MOD q] := by
  obtain ⟨_, _, h⟩ := maynardTaoBFT l hl
  obtain ⟨m, hm, hcong, _⟩ := h q hq a (by simpa using haq.gcd_eq_one) N
  exact ⟨m, hm, fun i hi => Int.natCast_modEq_iff.mp (hcong i hi)⟩

/-- **Linnik's theorem (divisibility form).**
There exist absolute constants `C, L ≥ 1` such that for every `M ≥ 1`,
there exists a prime `ℓ` with `M ∣ ℓ - 1` and `ℓ ≤ C · M^L`.

This is the divisibility-form version of Linnik 1944 (best `L = 5` due to
Xylouris 2011), in the form most convenient for lower-bound constructions. -/
theorem linnik_dvd :
  ∃ C : ℝ, ∃ L : ℕ, 1 ≤ C ∧ 1 ≤ L ∧
    ∀ M : ℕ, 1 ≤ M →
      ∃ ℓ : ℕ, Nat.Prime ℓ ∧ M ∣ ℓ - 1 ∧ (ℓ : ℝ) ≤ C * (M : ℝ) ^ L :=
  Linnik.exists_polynomial_prime_dvd_sub_one
