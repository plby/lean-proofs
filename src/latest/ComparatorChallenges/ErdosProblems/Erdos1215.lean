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

open Set

namespace Erdos1215

theorem not_erdos_1215 :
    ¬ ∃ C : ℝ, ∀ P : Polynomial ℂ,
      (P.eval 0 = 1 ∧ 0 < P.natDegree ∧
        ∀ z : ℂ, P.IsRoot z → ‖z‖ = 1) →
      ∃ γ : ℝ → ℂ,
        (ContinuousOn γ (Icc 0 1) ∧ γ 0 = 0 ∧ ‖γ 1‖ = 1 ∧
          ∀ t ∈ Icc (0 : ℝ) 1, t ≠ 0 → ‖P.eval (γ t)‖ < 1) ∧
        eVariationOn γ (Icc 0 1) ≤ ENNReal.ofReal C := by
  sorry

end Erdos1215
