/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Shortlex
import Mathlib.Data.List.SplitBy
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Pairing
import Mathlib.Order.RelIso.Set
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Erdős Problem 590

Chang's partition relation `ω ^ ω → (ω ^ ω, 3)²`.
-/

open Cardinal Ordinal

universe u

/-- The mixed ordinal/cardinal partition relation `α → (β, c)²`. -/
def OrdinalCardinalRamsey (α β : Ordinal.{u}) (c : Cardinal.{u}) : Prop :=
  ∀ red blue : SimpleGraph α.ToType, IsCompl red blue →
    (∃ s, red.IsClique s ∧ typeLT s = β) ∨
      ∃ s, blue.IsClique s ∧ #s = c

namespace Erdos590

theorem erdos_590 :
    OrdinalCardinalRamsey (ω ^ ω : Ordinal.{u})
      (ω ^ ω : Ordinal.{u}) (3 : Cardinal.{u}) := by
  sorry

end Erdos590
