import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Real derivatives of genuinely holomorphic scalar functions

Restricting the actual complex derivative to real scalars identifies its
directional values with multiplication by the complex derivative. Complex
differentiability on an open set supplies analyticity, holomorphicity of
every iterated derivative, and real smoothness on that same open set.
-/

noncomputable section

open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse

variable {V : Set ℂ} {g : ℂ → ℂ}

/-- The real Fréchet derivative is the genuine complex derivative restricted to real scalars. -/
theorem real_fderiv_apply_eq_complex_deriv {z : ℂ}
    (hg : DifferentiableAt ℂ g z) (v : ℂ) :
    fderiv ℝ g z v = deriv g z * v := by
  rw [(hg.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  change v * deriv g z = deriv g z * v
  exact mul_comm _ _

/-- Pointwise restriction of scalars at any point of the original holomorphic domain. -/
theorem holomorphic_fderiv_apply (hV : IsOpen V) (hg : DifferentiableOn ℂ g V)
    (z : ℂ) (hz : z ∈ V) (v : ℂ) :
    fderiv ℝ g z v = deriv g z * v :=
  real_fderiv_apply_eq_complex_deriv (hg.differentiableAt (hV.mem_nhds hz)) v

/-- The original holomorphicity assumption supplies analyticity of every complex derivative. -/
theorem holomorphic_iteratedDeriv_analyticOnNhd (hV : IsOpen V)
    (hg : DifferentiableOn ℂ g V) (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv n g) V := by
  rw [iteratedDeriv_eq_iterate]
  exact (hg.analyticOnNhd hV).iterated_deriv n

/-- All iterated complex derivatives are holomorphic on the same original open domain. -/
theorem holomorphic_iteratedDeriv (hV : IsOpen V) (hg : DifferentiableOn ℂ g V)
    (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n g) V :=
  (holomorphic_iteratedDeriv_analyticOnNhd hV hg n).differentiableOn

/-- Real smoothness follows from actual holomorphicity, with no extra regularity hypothesis. -/
theorem holomorphic_contDiffOn_real (hV : IsOpen V) (hg : DifferentiableOn ℂ g V) :
    ContDiffOn ℝ ∞ g V :=
  (hg.contDiffOn hV : ContDiffOn ℂ ∞ g V).restrict_scalars ℝ

/-- Each genuine iterated complex derivative is also real smooth on the original domain. -/
theorem holomorphic_iteratedDeriv_contDiffOn_real (hV : IsOpen V)
    (hg : DifferentiableOn ℂ g V) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n g) V :=
  holomorphic_contDiffOn_real hV (holomorphic_iteratedDeriv hV hg n)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse
