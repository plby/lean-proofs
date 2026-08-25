/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 490.
https://www.erdosproblems.com/forum/thread/490

Informal authors of the original argument:
- Endre Szemerédi
- ChatGPT 5.5 Pro

Formal authors of the original formalization:
- Aristotle
- Wouter van Doorn

Axiom-free analytic replacement and rectangle-counting proof: Codex.

URLs for the original argument and formalization:
- https://www.erdosproblems.com/forum/thread/490#post-6497
- https://github.com/Woett/Lean-files/blob/main/ErdosProblem490.lean
-/

import ErdosProblems.Erdos490.Assembly
import ErdosProblems.Erdos490.ParameterProduct

/-!
# Erdős problem 490, with constant 60 and no additional axioms

The proof uses an elementary factorial estimate for the Chebyshev function,
the proved Mertens product theorem, a weighted deletion argument, and disjoint
quotient rectangles. Dyadic layers and a kernel-checked finite Euler-product
certificate give an asymptotic constant below 60. No explicit Dusart estimates
are assumed. See the submodules for the analytic and numerical details.
-/

namespace Erdos490

/-- If n is large enough, then every n-admissible pair satisfies
    |A|·|B| < 60 · n²/log n. -/
theorem erdos_490 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ A B : Finset ℕ,
        A ⊆ Finset.Icc 1 n → B ⊆ Finset.Icc 1 n →
        (∀ a₁ ∈ A, ∀ b₁ ∈ B, ∀ a₂ ∈ A, ∀ b₂ ∈ B,
          a₁ * b₁ = a₂ * b₂ → a₁ = a₂ ∧ b₁ = b₂) →
        A.card * B.card < 60 * n ^ 2 / Real.log n := by
  obtain ⟨N₀, hN₀⟩ := rectangle_layer_bound rectangleMultiplicity rectangleGrowth
    rectangleGrowth_ge_one rectangleGrowth_tendsto rectangle_log_summable
    rectangle_weights_summable (by linarith [rectangle_weightTotal_lt]) 60 rectangle_constant_lt
  exact ⟨N₀, fun n hn A B hA hB hinj => hN₀ n hn A B ⟨hA, hB, hinj⟩⟩

#print axioms erdos_490

end Erdos490

alias _root_.Erdos490.main_theorem := _root_.Erdos490.erdos_490
