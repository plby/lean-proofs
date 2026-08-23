/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Tactic

open MeasureTheory Polynomial Set
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

attribute [-instance] CommCStarAlgebra.toNormedCommRing

namespace Erdos515

open scoped Classical in
def IsPolynomialFunction (f : ℂ → ℂ) : Prop :=
  ∃ p : ℂ[X], ∀ z : ℂ, p.eval z = f z

end Erdos515

namespace Erdos515

open scoped Classical in
noncomputable def segmentPoint (a b : ℂ) (t : ℝ) : ℂ :=
  AffineMap.lineMap a b t

end Erdos515

namespace Erdos515

open scoped Classical in
structure LocallyRectifiablePath where
  vertex : ℕ → ℂ
  tendsToInfinity : ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) 1,
    R ≤ ‖segmentPoint (vertex n) (vertex (n + 1)) t‖

end Erdos515

namespace Erdos515

open scoped Classical in
noncomputable def inverseNormDensity (f : ℂ → ℂ) (lambda : ℝ) (a b : ℂ) (t : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖f (segmentPoint a b t)‖) ^ (-lambda)

end Erdos515

namespace Erdos515

open scoped Classical in
noncomputable def segmentIntegral (f : ℂ → ℂ) (lambda : ℝ) (a b : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖b - a‖ *
    ∫⁻ t in Icc (0 : ℝ) 1, inverseNormDensity f lambda a b t

end Erdos515

namespace Erdos515

open scoped Classical in
noncomputable def lineIntegral
    (C : LocallyRectifiablePath) (f : ℂ → ℂ) (lambda : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, segmentIntegral f lambda (C.vertex n) (C.vertex (n + 1))

end Erdos515

namespace Erdos515

attribute [local instance] CommCStarAlgebra.toNormedCommRing

open scoped Classical in
theorem erdos_515 {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (htrans : ¬ IsPolynomialFunction f) :
    ∃ C : LocallyRectifiablePath,
      ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ⊤ := by
  sorry

end Erdos515

end
