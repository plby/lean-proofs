/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 219.
https://www.erdosproblems.com/forum/thread/219

Informal authors:
- Ben Green
- Terence Tao

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos219.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/219.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Wikipedia.GreenTao
import Wikipedia.SzemeredisTheorem.FormalConjectures139

namespace Erdos219

/-- The set of nonempty arithmetic progressions consisting entirely of primes. -/
def primeArithmeticProgressions : Set (Set ℕ) :=
  {s | (∀ p ∈ s, p.Prime) ∧ ∃ l > 0, s.IsAPOfLength l}

/-- Erdős Problem 219: there are arbitrarily long arithmetic progressions of primes. -/
theorem erdos_219 :
    ∀ N : ℕ, ∃ l ∈ primeArithmeticProgressions, N ≤ ENat.card l := by
  intro N
  let L : ℕ := max 1 N
  obtain ⟨a, b, hb, hmem⟩ := GreenTao.green_tao L
  let s : Set ℕ := {x | ∃ i : ℕ, i < L ∧ x = a + i * b}
  have hAP : s.IsAPOfLength (L : ℕ∞) :=
    SzemeredisTheorem.arithmeticProgressionSet_isAP a b L (by omega)
  refine ⟨s, ?_, ?_⟩
  · refine ⟨?_, ⟨(L : ℕ∞), ?_, hAP⟩⟩
    · intro p hp
      rcases hp with ⟨i, hi, rfl⟩
      simpa [Nat.mul_comm] using hmem i hi
    · exact_mod_cast (show 0 < L by dsimp [L]; omega)
  · rw [hAP.card]
    exact_mod_cast (show N ≤ L from le_max_right 1 N)

end Erdos219
