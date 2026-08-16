/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Erdős Problem 1077

The literal upstream statement about balanced subgraphs has a negative answer.
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

theorem erdos_1077 :
    answer(False) ↔ ∀ ε > (0 : ℝ), ε < 1 → ∀ α > (0 : ℝ), α < 1 →
      ∀ᶠ D in atTop, ∀ᶠ n in atTop,
        ∀ G : SimpleGraph (Fin n),
          G.edgeSet.ncard > (n : ℝ) ^ (1 + α) →
            ∃ (H : Subgraph G),
              letI m := H.verts.ncard
              IsBalanced H.coe D ∧
                m > (n : ℝ) ^ (1 - α) ∧
                  H.edgeSet.ncard > ε * m ^ (1 + α) := by
  sorry
