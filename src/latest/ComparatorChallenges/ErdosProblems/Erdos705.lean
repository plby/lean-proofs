/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open scoped EuclideanGeometry

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

syntax (name := answerSyntax705) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

namespace SimpleGraph

def UnitDistancePlaneGraph (V : Set (EuclideanSpace ℝ (Fin 2))) : SimpleGraph V where
  Adj x y := Dist.dist x y = 1
  symm := ⟨by
    intro x y hxy
    simpa [PseudoMetricSpace.dist_comm] using hxy⟩
  loopless := ⟨by
    intro x hxx
    simpa using hxx⟩

end SimpleGraph

namespace Erdos705

open SimpleGraph

theorem erdos_705 :
    answer(False) ↔ ∃ k, ∀ V : Set ℝ², V.Finite →
      (UnitDistancePlaneGraph V).girth ≥ k →
      (UnitDistancePlaneGraph V).chromaticNumber ≤ 3 := by
  sorry

end Erdos705
