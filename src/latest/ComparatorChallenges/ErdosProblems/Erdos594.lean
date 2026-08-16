/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 594

Every graph with no countable proper coloring contains all sufficiently large
odd cycles.  The mathematical proof and the correspondence between its lemmas
and this development are in `tex/594.tex`.
-/

syntax (name := answerSyntax594) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

open Function Set SimpleGraph
open scoped Ordinal

namespace Erdos594

noncomputable section

attribute [local instance] Classical.propDecidable


variable {V : Type*}

/-- A graph is uncountably chromatic when it has no coloring by natural numbers. -/
def IsUncountablyChromatic (G : SimpleGraph V) : Prop :=
  IsEmpty (G.Coloring ℕ)

end

end Erdos594

theorem erdos_594 : answer(True) ↔
    ∀ (V : Type) (G : SimpleGraph V), IsEmpty (G.Coloring ℕ) →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = 2 * k + 1 := by
  sorry
