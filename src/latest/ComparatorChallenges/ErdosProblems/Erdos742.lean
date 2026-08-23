/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 742

Füredi's sufficiently-large resolution of the Murty--Simon conjecture for
diameter-two edge-critical graphs.

The detailed mathematical proof and a Leanization map are in `tex/742.tex`.
-/

open scoped ENat
open SimpleGraph

namespace Erdos742

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

def IsDiameter2Critical (G : SimpleGraph V) : Prop :=
  G.diam = 2 ∧ ∀ e ∈ G.edgeSet, (G.deleteEdges {e}).diam ≠ 2

theorem furedi_bound : ∃ n₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    n₀ ≤ Fintype.card V → IsDiameter2Critical G →
      G.edgeFinset.card ≤ (Fintype.card V) ^ 2 / 4 := by
  sorry
