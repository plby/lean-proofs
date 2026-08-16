/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

namespace SzemeredisTheorem

/-- A set contains arithmetic progressions of every finite length. -/
def ContainsArbitraryAPs (A : Set ℕ) : Prop :=
  ∀ k : ℕ, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ A

end SzemeredisTheorem

namespace GreenTao

/-- The natural primes contain arbitrarily long arithmetic progressions. -/
theorem green_tao :
    SzemeredisTheorem.ContainsArbitraryAPs {p : ℕ | Nat.Prime p} := by
  sorry

end GreenTao
