import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspAxes
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspCovectors

/-!
# Actual vanishing analytic coefficients on the filled toric axes

These coefficient germs are evaluations of the genuine global-form
pullback in the reference toric chart. Multiplication by the coordinate
parameter gives an analytic germ vanishing at zero. The three identities
below identify these germs with evaluations on the exact reference
Jacobian columns, including all powers of the normalized exponential
factor and the positive orientation sign.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open ToricCharts HolomorphicDifferentialForms

local notation "E₃" => CoordinateSpace 3
local notation "EL" => ℂ × ComplexPlane₂
local notation "K" => (2 * Real.pi * Complex.I : ℂ)
local notation "e₀" => (Pi.single (0 : Fin 3) (1 : ℂ) : E₃)
local notation "e₁" => (Pi.single (1 : Fin 3) (1 : ℂ) : E₃)
local notation "e₂" => (Pi.single (2 : Fin 3) (1 : ℂ) : E₃)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The actual reference-axis coefficient with its exact exponential factor and one parameter. -/
def vanishingAxisCoefficient {p : ℕ} (θ : Form EL Threefold.Space p)
    (k : Fin 3) (v : Fin p → E₃) (q : ℂ) : ℂ :=
  (K ^ p * q) * axisCoefficientExtension θ k v q

/-- This is a proved analytic germ, extracted from the original holomorphic form. -/
theorem vanishingAxisCoefficient_analyticAt_zero {p : ℕ} (θ : Form EL Threefold.Space p)
    (k : Fin 3) (v : Fin p → E₃) : AnalyticAt ℂ (vanishingAxisCoefficient θ k v) 0 :=
  (analyticAt_const.mul analyticAt_id).mul (axisCoefficientExtension_analyticAt_zero θ k v)

@[simp] theorem vanishingAxisCoefficient_zero {p : ℕ} (θ : Form EL Threefold.Space p)
    (k : Fin 3) (v : Fin p → E₃) : vanishingAxisCoefficient θ k v 0 = 0 := by
  simp only [vanishingAxisCoefficient, mul_zero, zero_mul]

/-- The one-covector evaluation along the exact transverse tangent. -/
theorem one_reference_axis_evaluation (θ : Form EL Threefold.Space 1)
    (k : Fin 3) (q : CuspQuotient.disc CuspGeometry.data.radius) :
    referenceCoefficient θ ![(K * (q : ℂ)) • (Pi.single k 1 : E₃)] (axisInclusion k q) =
      vanishingAxisCoefficient θ k ![(Pi.single k 1 : E₃)] q := by
  rw [vanishingAxisCoefficient, axisCoefficientExtension_of_mem θ k _ q.property, pow_one]
  exact oneCovector_scaled_basis
    (nativeCoefficients E₃ referenceDomain (referencePullback θ) (axisInclusion k q)) K q k

/-- Both genuine mixed-covector evaluations have the positive factor `(2πi)^2 q`. -/
theorem two_reference_axis_evaluation (θ : Form EL Threefold.Space 2)
    (i : Fin 2) (q : CuspQuotient.disc CuspGeometry.data.radius) :
    referenceCoefficient θ
        ![(K * (q : ℂ)) • e₀, -(K * (q : ℂ)) • e₀ + K • (Pi.single i.succ 1 : E₃)]
        (axisInclusion 0 q) =
      vanishingAxisCoefficient θ 0 ![e₀, (Pi.single i.succ 1 : E₃)] q := by
  rw [vanishingAxisCoefficient, axisCoefficientExtension_of_mem θ 0 _ q.property]
  exact twoCovector_referenceJacobian
    (nativeCoefficients E₃ referenceDomain (referencePullback θ) (axisInclusion 0 q)) K q i.succ

/-- The top-covector evaluation has the positive factor `(2πi)^3 q`, not `q^2`. -/
theorem three_reference_axis_evaluation (θ : Form EL Threefold.Space 3)
    (q : CuspQuotient.disc CuspGeometry.data.radius) :
    referenceCoefficient θ
        ![(K * (q : ℂ)) • e₀, -(K * (q : ℂ)) • e₀ + K • e₁,
          -(K * (q : ℂ)) • e₀ + K • e₂] (axisInclusion 0 q) =
      vanishingAxisCoefficient θ 0 ![e₀, e₁, e₂] q := by
  rw [vanishingAxisCoefficient, axisCoefficientExtension_of_mem θ 0 _ q.property]
  exact threeCovector_referenceJacobian
    (nativeCoefficients E₃ referenceDomain (referencePullback θ) (axisInclusion 0 q)) K q

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
