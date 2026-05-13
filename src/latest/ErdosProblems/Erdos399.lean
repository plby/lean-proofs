/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import Mathlib

theorem erdos_399 : False ↔
    ¬ ∃ (n x y k : ℕ), 1 < x * y ∧ 2 < k ∧
      (Nat.factorial n = x ^ k + y ^ k ∨ Nat.factorial n + y ^ k = x ^ k) := by
  simp only [false_iff, Classical.not_not]
  exact ⟨10, 48, 36, 4, by decide⟩
