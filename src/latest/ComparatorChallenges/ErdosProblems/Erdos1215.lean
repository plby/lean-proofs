/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.Topology.Connected.Clopen
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Erdős Problem 1215

Mac Lane's negative answer to the question whether paths in the strict
sublevel set of a polynomial whose roots lie on the unit circle have a
universal length bound.

The strict inequality is imposed away from the initial parameter: the
historical statement explicitly excludes the origin, where the normalization
`P(0) = 1` makes strict sublevel membership impossible.

The detailed mathematical proof and Leanization map are in `tex/1215.tex`.
-/

open Set Metric
open scoped ENNReal Topology BigOperators

noncomputable section

namespace Erdos1215

/-- A normalized, nonconstant polynomial all of whose roots lie on the complex
unit circle. -/
def IsAdmissible (P : Polynomial ℂ) : Prop :=
  P.eval 0 = 1 ∧
    0 < P.natDegree ∧
      ∀ z : ℂ, P.IsRoot z → ‖z‖ = 1

/-- An endpoint-correct escape path.  The value at `t = 0` is excluded from
the strict sublevel condition, exactly as in the original formulation. -/
def IsEscapePath (P : Polynomial ℂ) (γ : ℝ → ℂ) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧
    γ 0 = 0 ∧
      ‖γ 1‖ = 1 ∧
        ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → ‖P.eval (γ t)‖ < 1

/-- Extended total variation on the parameter interval.  Nonrectifiable paths
have infinite extended length. -/
def PathELength (γ : ℝ → ℂ) : ℝ≥0∞ :=
  eVariationOn γ (Icc 0 1)

/-- The positive assertion asked in Problem 1215. -/
def HasUniformEscapeBound : Prop :=
  ∃ C : ℝ, ∀ P : Polynomial ℂ, IsAdmissible P →
    ∃ γ : ℝ → ℂ, IsEscapePath P γ ∧ PathELength γ ≤ ENNReal.ofReal C

/-- The stronger form of Mac Lane's counterexample statement. -/
def HasArbitrarilyLongCounterexamples : Prop :=
  ∀ L : ℝ, 0 ≤ L →
    ∃ P : Polynomial ℂ, IsAdmissible P ∧
      ∀ γ : ℝ → ℂ, IsEscapePath P γ → ENNReal.ofReal L < PathELength γ

theorem erdos_1215 :
    ¬ ∃ C : ℝ, ∀ P : Polynomial ℂ,
      (P.eval 0 = 1 ∧ 0 < P.natDegree ∧
        ∀ z : ℂ, P.IsRoot z → ‖z‖ = 1) →
      ∃ γ : ℝ → ℂ,
        (ContinuousOn γ (Icc 0 1) ∧ γ 0 = 0 ∧ ‖γ 1‖ = 1 ∧
          ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → ‖P.eval (γ t)‖ < 1) ∧
        eVariationOn γ (Icc 0 1) ≤ ENNReal.ofReal C := by
  sorry

end Erdos1215

end
