import Mathlib

/- Ported to Lean/Mathlib 4.33.0; imports and proof elaboration adapted. -/
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Erdős Problem 768 — core definitions

This file sets up the basic objects for the formalisation of Eric Li's paper
*The Sylow Divisor Condition: a Resolution of Erdős Problem 768* (arXiv:2606.24872).

An integer `n` satisfies the **Sylow divisor condition** if, for every prime
`p ∣ n`, there is a divisor `d ∣ n` with `d > 1` and `d ≡ 1 (mod p)`.  We let
`Acal` denote the set of such integers and `Acount x = #{ n ≤ x : n ∈ Acal }`.

The main theorem (see `ErdosProblems.Erdos768.Main`) is
`lim_{x→∞} log(x / A(x)) / (√(log x) · log log x) = 1 / (2√(log 2))`.
-/

open scoped Classical BigOperators

namespace Erdos768

/-- The **Sylow divisor condition**: for every prime `p ∣ n` there is a divisor
`d ∣ n` with `d > 1` and `d ≡ 1 (mod p)`.  The integer `1` satisfies this
vacuously. -/
def SylowDivisor (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → ∃ d : ℕ, d ∣ n ∧ 1 < d ∧ d % p = 1

/-- The set `𝒜` of integers satisfying the Sylow divisor condition. -/
def Acal : Set ℕ := {n | SylowDivisor n}

/-- `A(x) = #{ n ≤ x : n ∈ 𝒜 }`, the counting function of the Sylow divisor
condition on the interval `[1, x]`. -/
noncomputable def Acount (x : ℝ) : ℕ :=
  ((Finset.Icc 1 ⌊x⌋₊).filter SylowDivisor).card

/-- The constant `c₀ = 1 / (2√(log 2))` appearing in the answer to Problem 768. -/
noncomputable def c₀ : ℝ := 1 / (2 * Real.sqrt (Real.log 2))

/-- The scale `S(x) = √(log x) · log log x`. -/
noncomputable def Sscale (x : ℝ) : ℝ := Real.sqrt (Real.log x) * Real.log (Real.log x)

/-- The ordered `k`-fold divisor function
`d_k(n) = #{ (n₁,…,n_k) : n₁⋯n_k = n }`.  For `n ≥ 1` each factor divides `n`,
so we may search inside `(divisors n)^k`. -/
noncomputable def dk (k n : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => n.divisors)).filter
    (fun f => ∏ i, f i = n)).card

/-- The number of distinct prime factors, `ω(n) = #{ p prime : p ∣ n }`. -/
abbrev omegaCount (n : ℕ) : ℕ := n.primeFactors.card

/-- The number of divisors, `τ(n) = #{ d : d ∣ n }`. -/
abbrev tauCount (n : ℕ) : ℕ := n.divisors.card

/-- The radical `rad(n) = ∏_{p ∣ n} p`. -/
abbrev rad (n : ℕ) : ℕ := n.primeFactors.prod id

/-- `s_r = 1 + ⌊log₂ r⌋`, the length of the canonical homogeneous subsequence. -/
def sr (r : ℕ) : ℕ := 1 + Nat.log 2 r

/-- `h_r = ⌊s_r / 2⌋`, the number of prefix rows used in the compression. -/
def hr (r : ℕ) : ℕ := sr r / 2

/-- `H_t = ⌈log(t+2)/(2 log 2)⌉ + 3`, a uniform bound for `h_r` over `r ≤ t`.
The additive constant `3` is a safety margin ensuring `h_r ≤ H_t` uniformly for
every `r ≤ t` and absorbing the one-prime branch and small values of `t`. -/
noncomputable def Ht (t : ℕ) : ℕ := ⌈Real.log (t + 2) / (2 * Real.log 2)⌉₊ + 3

end Erdos768
