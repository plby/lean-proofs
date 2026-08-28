import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspAxisCoefficients
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspReferencePullback

/-!
# Logarithmic pullback coefficients extend through the actual filled cusp

The genuine logarithmic pullback is computed through the reference toric
chart. Evaluating its exact Jacobian along the three transverse curves
identifies the native coefficients with the analytic vanishing functions
already extracted from the filled chart. No coefficient extension or
factorization is an input to these statements.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open ToricCharts CuspUniformization CuspFamily HolomorphicDifferentialForms

local notation "E₃" => CoordinateSpace 3
local notation "EL" => ℂ × ComplexPlane₂
local notation "K" => (2 * Real.pi * Complex.I : ℂ)
local notation "e₀" => (Pi.single (0 : Fin 3) (1 : ℂ) : E₃)
local notation "e₁" => (Pi.single (1 : Fin 3) (1 : ℂ) : E₃)
local notation "e₂" => (Pi.single (2 : Fin 3) (1 : ℂ) : E₃)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The logarithmic curves land on the actual filled reference axes. -/
theorem refExpInto_logAxisPoint (k : Fin 3) (s : LogBase CuspGeometry.data.radius) :
    refExpInto (logAxisPoint k s) = axisInclusion k ⟨exponential s, s.property⟩ := by
  apply Subtype.ext
  exact refExp_logAxisPoint k s

/-- Each one-form curve evaluation is an actual analytic function of the cusp
parameter which vanishes at zero. -/
theorem one_logAxis_evaluation (θ : Form EL Threefold.Space 1)
    (k : Fin 3) (s : LogBase CuspGeometry.data.radius) :
    logCoefficients θ (logAxisPoint k s) ![logAxisDirection k] =
      vanishingAxisCoefficient θ k ![(Pi.single k 1 : E₃)] (exponential s) := by
  rw [logCoefficients_refExp]
  have hv : (fun j : Fin 1 => refExpDerivative (logAxisPoint k s)
      (![logAxisDirection k] j)) = ![(K * exponential s) • (Pi.single k 1 : E₃)] := by
    funext j
    fin_cases j
    exact refExpDerivative_logAxisPoint k s
  rw [hv, refExpInto_logAxisPoint]
  exact one_reference_axis_evaluation θ k ⟨exponential s, s.property⟩

/-- In particular the normalized horizontal coefficient is analytic and vanishing at the cusp. -/
theorem one_logBase_evaluation (θ : Form EL Threefold.Space 1)
    (s : LogBase CuspGeometry.data.radius) :
    logCoefficients θ (logPoint s 0) ![(1, 0)] =
      vanishingAxisCoefficient θ 0 ![e₀] (exponential s) :=
  one_logAxis_evaluation θ 0 s

/-- Both mixed two-form coefficients are the actual vanishing filled-axis coefficients. -/
theorem two_logMixed_evaluation (θ : Form EL Threefold.Space 2)
    (s : LogBase CuspGeometry.data.radius) (i : Fin 2) :
    logCoefficients θ (logPoint s 0) ![(1, 0), (0, Pi.single i 1)] =
      vanishingAxisCoefficient θ 0 ![e₀, (Pi.single i.succ 1 : E₃)] (exponential s) := by
  rw [logCoefficients_refExp]
  have hv : (fun j : Fin 2 => refExpDerivative (logPoint s 0)
      (![(1, 0), (0, Pi.single i 1)] j)) =
      ![(K * exponential s) • e₀,
        -(K * exponential s) • e₀ + K • (Pi.single i.succ 1 : E₃)] := by
    funext j
    fin_cases j
    · exact refExpDerivative_logPoint_base s
    · exact refExpDerivative_logPoint_fibre s i
  rw [hv]
  have he : refExpInto (logPoint s 0) = axisInclusion 0 ⟨exponential s, s.property⟩ :=
    refExpInto_logAxisPoint 0 s
  rw [he]
  exact two_reference_axis_evaluation θ i ⟨exponential s, s.property⟩

/-- The top coefficient has the source's exact first-order parameter factor. -/
theorem three_logTop_evaluation (θ : Form EL Threefold.Space 3)
    (s : LogBase CuspGeometry.data.radius) :
    logCoefficients θ (logPoint s 0)
        ![(1, 0), (0, Pi.single (0 : Fin 2) 1), (0, Pi.single (1 : Fin 2) 1)] =
      vanishingAxisCoefficient θ 0 ![e₀, e₁, e₂] (exponential s) := by
  rw [logCoefficients_refExp]
  have hv : (fun j : Fin 3 => refExpDerivative (logPoint s 0)
      (![(1, 0), (0, Pi.single (0 : Fin 2) 1), (0, Pi.single (1 : Fin 2) 1)] j)) =
      ![(K * exponential s) • e₀, -(K * exponential s) • e₀ + K • e₁,
        -(K * exponential s) • e₀ + K • e₂] := by
    funext j
    fin_cases j
    · exact refExpDerivative_logPoint_base s
    · exact refExpDerivative_logPoint_fibre s 0
    · exact refExpDerivative_logPoint_fibre s 1
  rw [hv]
  have he : refExpInto (logPoint s 0) = axisInclusion 0 ⟨exponential s, s.property⟩ :=
    refExpInto_logAxisPoint 0 s
  rw [he]
  exact three_reference_axis_evaluation θ ⟨exponential s, s.property⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
