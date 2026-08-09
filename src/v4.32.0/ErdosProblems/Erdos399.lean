/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 399.
https://www.erdosproblems.com/forum/thread/399

Informal authors:
- Jonas Barfield

Formal authors:
- Codex
- Cong Lu

URLs:
- https://github.com/google-deepmind/formal-conjectures/commit/ce390075c49403db77b955a3f3a8bf4c4de99cbe
-/
import Mathlib

namespace Erdos399


theorem erdos_399 : False ↔
    ¬ ∃ (n x y k : ℕ), 1 < x * y ∧ 2 < k ∧
      (Nat.factorial n = x ^ k + y ^ k ∨ Nat.factorial n + y ^ k = x ^ k) := by
  simp only [false_iff, Classical.not_not]
  exact ⟨10, 48, 36, 4, by decide⟩

#print axioms erdos_399
-- 'Erdos399.erdos_399' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos399
