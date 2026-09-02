/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 327.
https://www.erdosproblems.com/forum/thread/327

Informal authors:
- Donald Della Pietra
- Will Sawin
- GPT-5.6 Sol

Formal authors:
- Donald Della Pietra
- GPT-5.6 Sol

URLs:
- https://www.erdosproblems.com/forum/thread/327/proof-claims#proof-claim-168
- https://github.com/donalddellapietra/erdos-327-proof/releases/download/proof-claim-v1/erdos-327-lean-formalization-v1.zip
- https://github.com/donalddellapietra/erdos-327-proof/blob/5c6db2f53668edd621ec75d48821113345565ede/lean/Erdos327/Analytic/Unconditional.lean
- https://github.com/donalddellapietra/erdos-327-proof/blob/5c6db2f53668edd621ec75d48821113345565ede/paper/main.tex
- https://github.com/teorth/mathlib4/blob/da1f94df976c7cd38117281c57d6ee3046c8d104/Mathlib/NumberTheory/Mertens.lean
-/
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
