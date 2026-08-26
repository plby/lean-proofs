/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Formalization by Donald Della Pietra with GPT-5.6 Sol.
Source: https://github.com/donalddellapietra/erdos-327-proof/releases/tag/proof-claim-v1
Original Lean version: 4.33.0-rc1. See Erdos327/README.md for provenance.
-/
import ErdosProblems.Erdos327.Proof

namespace Erdos327

theorem erdos_327 :
    (∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ a + b ∣ a * b) ∧
        (1 / 2 + ε) * (N : ℝ) ≤ (A.card : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ a + b ∣ 2 * a * b) ∧
        c * (N : ℝ) ≤ (A.card : ℝ)) :=
  Analytic.erdos327FullConclusion_unconditional

end Erdos327
