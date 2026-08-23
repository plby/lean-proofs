/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 1185

The proposed uniform statement is false already for three-term arithmetic
progressions.  We give a finite periodic form of Furstenberg's quadratic
skew-shift counterexample.  The detailed mathematical proof and the
Leanization map are in `tex/1185.tex`.
-/

namespace Erdos1185

open scoped BigOperators

/-- `A` contains a nonconstant `k`-term arithmetic progression whose
positive common difference is a difference of two elements of `B`. -/
def HasAPWithStepInDiff (k : ℕ) (A B : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧
    (∀ j : ℕ, j < k → a + j * d ∈ A) ∧
    ∃ b₁ ∈ B, ∃ b₂ ∈ B, d = b₁ - b₂

/-- The literal universal affirmative assertion in Erdős Problem 1185. -/
def Erdos1185Statement : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k →
    ∃ m : ℕ, 1 ≤ m ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A B : Finset ℕ,
        A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
        δ * (N : ℝ) ≤ (A.card : ℝ) → m ≤ B.card →
        HasAPWithStepInDiff k A B

/-! ## The rapidly divisible sequence -/

/-- The rapidly growing sequence used to make all pairwise quadratic
phases lie in one fixed arc. -/
def rapidB : ℕ → ℕ
  | 0 => 27
  | n + 1 => 27 * (rapidB n) ^ 2

@[simp] lemma rapidB_zero : rapidB 0 = 27 := rfl

@[simp] lemma rapidB_succ (n : ℕ) : rapidB (n + 1) = 27 * (rapidB n) ^ 2 := rfl


theorem erdos_1185 : ¬ Erdos1185Statement := by
  sorry

end Erdos1185
