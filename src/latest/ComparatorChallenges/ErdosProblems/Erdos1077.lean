/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 1077

The literal upstream statement has a negative answer.  The complete bipartite
graph `K_{2k, k^4 - 2k}` has more than `(k^4)^(5/4)` edges, while every
nonempty `D`-balanced subgraph has at most `2 * (D + 1) * k` vertices.

The detailed mathematical proof and Leanization map are in `tex/1077.tex`.
-/

syntax (name := answerSyntax1077) "answer(" term ")" : term
macro_rules | `(answer($t)) => `($t)

namespace SimpleGraph

/-- A finite graph is `D`-balanced when its maximum degree is at most `D`
times its minimum degree.  This is the definition used by the upstream
Formal Conjectures statement. -/
def IsBalanced {V : Type*} [Fintype V] (G : SimpleGraph V) (D : ℝ)
    [DecidableRel G.Adj] : Prop :=
  G.maxDegree ≤ D * G.minDegree

end SimpleGraph

namespace Erdos1077

open Finset Filter SimpleGraph

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The real-power identity used for the edge threshold. -/

theorem erdos_1077 :
    answer(False) ↔ ∀ ε > (0 : ℝ), ε < 1 → ∀ α > (0 : ℝ), α < 1 →
      ∀ᶠ D in atTop, ∀ᶠ n in atTop,
        ∀ G : SimpleGraph (Fin n),
          G.edgeSet.ncard > (n : ℝ) ^ (1 + α) →
            ∃ (H : Subgraph G),
              letI m := by
  sorry

