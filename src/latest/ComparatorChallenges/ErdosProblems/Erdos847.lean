/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import «_scratch».Erdos847Construction

/-!
# Erdős Problem 847

The negative solution is due to Christian Reiher, Vojtěch Rödl, and Marcelo Sales,
*Colouring versus density in integers and Hales--Jewett cubes* (2024).

The detailed mathematical proof and its Leanization map are in `tex/847.tex`.
-/

syntax (name := answerSyntax847) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

namespace Erdos847

open Set

attribute [local instance] Classical.propDecidable

/-- `HasFew3APs A` is the local positive-proportion hypothesis in the upstream statement. -/
def HasFew3APs (A : Set ℕ) : Prop :=
  ∃ ε : ℝ, ε > 0 ∧ ∀ B : Set ℕ, B ⊆ A → Finite B →
    ∃ C : Set ℕ, C ⊆ B ∧ C.ncard ≥ ε * B.ncard ∧ ThreeAPFree C

/-- A nonconstant monochromatic three-term arithmetic progression for a coloring of `A`. -/
def HasMonochromaticThreeAP (A : Set ℕ) {r : ℕ} (color : ℕ → Fin r) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a + c = b + b ∧ a ≠ c ∧ color a = color b ∧ color b = color c

/-- Every coloring of `A` by a nonempty finite palette has a monochromatic three-AP. -/
def RamseyForThreeAP (A : Set ℕ) : Prop :=
  ∀ r : ℕ, 0 < r → ∀ color : ℕ → Fin r, HasMonochromaticThreeAP A color

/-- The two properties supplied by the Reiher--Rödl--Sales counterexample. -/
def IsRRSCounterexample (A : Set ℕ) (μ : ℝ) : Prop :=
  RamseyForThreeAP A ∧
    ∀ B : Set ℕ, B ⊆ A → Finite B →
      ∃ C : Set ℕ, C ⊆ B ∧ C.ncard ≥ μ * B.ncard ∧ ThreeAPFree C

theorem erdos_847 : answer(False) ↔
    ∀ A : Set ℕ, Infinite A → HasFew3APs A →
      ∃ n, ∃ S : Fin n → Set ℕ,
        (∀ i, ThreeAPFree (S i)) ∧ A = ⋃ i : Fin n, S i := by
  sorry

