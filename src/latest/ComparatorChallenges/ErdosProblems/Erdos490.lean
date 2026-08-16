import Mathlib

attribute [local instance] Classical.propDecidable

open scoped BigOperators

axiom dusart_mertens_product (x : ℝ) (hx : x ≥ 2278382) :
    |∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime,
        (1 - 1 / (p : ℝ)) -
      1 / (Real.exp Real.eulerMascheroniConstant * Real.log x)| ≤
      1 / (5 * Real.exp Real.eulerMascheroniConstant * Real.log x ^ 4)

axiom dusart_pi_lower (x : ℝ) (hx : x ≥ 88789) :
    x / Real.log x + x / Real.log x ^ 2 + 2 * x / Real.log x ^ 3 ≤
      (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ)

axiom dusart_pi_upper (x : ℝ) (hx : x > 1) :
    (((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card : ℝ) ≤
      x / Real.log x + x / Real.log x ^ 2 + 2.53816 * x / Real.log x ^ 3

axiom dusart_chebyshev (x : ℝ) (hx : x ≥ 2) :
    |(∑ n ∈ Finset.range (⌊x⌋₊ + 1), ArithmeticFunction.vonMangoldt n) - x| <
      1.66 * x / Real.log x ^ 2

open Finset BigOperators Nat Real

namespace Erdos490

theorem main_theorem :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ,
        A ⊆ Finset.Icc 1 n → B ⊆ Finset.Icc 1 n →
        (∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B,
          a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂) →
        A.card * B.card < 60 * n ^ 2 / Real.log n := by
  sorry

end Erdos490
