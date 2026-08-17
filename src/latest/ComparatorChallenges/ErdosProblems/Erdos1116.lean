import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Pairing
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Contracting

open Filter Function Metric Set
open ComplexConjugate
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos1116

noncomputable def aPointCount (f : ℂ → ℂ) (r : ℝ) (a : ℂ) : ℕ :=
  ∑ᶠ z : ℂ,
    Int.toNat (MeromorphicOn.divisor (fun w ↦ f w - a) (ball 0 r) z)

end Erdos1116

namespace Erdos1116

def UnboundedCountRatio (f : ℂ → ℂ) (a b : ℂ) : Prop :=
  ∀ M : ℕ, ∀ R : ℝ, ∃ r : ℝ, R < r ∧
    0 < aPointCount f r b ∧
      M * aPointCount f r b < aPointCount f r a

end Erdos1116

namespace Erdos1116

theorem erdos_1116 :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ a b : ℂ, a ≠ b → UnboundedCountRatio f a b := by
  sorry

end Erdos1116

end
