import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeFamily
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterDerivativeIntegral

/-!
# The genuine base derivative of an actual Fourier coefficient

The differential is the normalized Haar integral of the actual base
differential. Evaluating it in any real base direction gives exactly the
Fourier coefficient of the genuinely smooth base-derivative family. All
domination and regularity hypotheses of the integral theorem are derived
from the original smooth family.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter

variable {U : Opens ℂ} {d : Type*} [Fintype d]

namespace SmoothFamily

variable (f : SmoothFamily U d)

/-- The original Fourier coefficient in the ambient original base coordinate. -/
def coefficientValue (k : d → ℤ) (z : ℂ) : ℂ :=
  mFourierCoeff (fun t => ambientValue f (z, t)) k

@[simp] theorem coefficientValue_apply (k : d → ℤ) (b : U) :
    f.coefficientValue k (b : ℂ) = mFourierCoeff (fun t => f (b, t)) k := by
  simp only [coefficientValue, ambientValue_apply]

/-- The actual joint base differential, bundled using its proved continuity. -/
def baseDifferentialMap : C(U × UnitAddTorus d, ℂ →L[ℝ] ℂ) :=
  ⟨f.baseDifferential, f.baseDifferential_continuous⟩

@[simp] theorem baseDifferentialMap_apply (p : U × UnitAddTorus d) :
    f.baseDifferentialMap p = f.baseDifferential p := rfl

/-- The actual Haar integral of the Fourier-weighted base differential. -/
def coefficientDifferential (k : d → ℤ) (b : U) : ℂ →L[ℝ] ℂ :=
  Derivative.fourierDifferential f.baseDifferentialMap k b

/-- Every directional value is exactly the coefficient of the genuine derivative family. -/
theorem coefficientDifferential_apply (k : d → ℤ) (b : U) (v : ℂ) :
    f.coefficientDifferential k b v =
      mFourierCoeff (fun t => f.baseDerivative v (b, t)) k := by
  rw [coefficientDifferential, Derivative.fourierDifferential_apply]
  rfl

/-- Full real Fréchet differentiation under the actual Haar Fourier integral. -/
theorem coefficientValue_hasFDerivAt (k : d → ℤ) (b : U) :
    HasFDerivAt (f.coefficientValue k) (f.coefficientDifferential k b) (b : ℂ) :=
  Derivative.hasFDerivAt_fourier_of_continuous_differential
    (ambientValue f) f.baseDifferentialMap f.ambientValue_continuous_fibre
    f.ambientValue_hasFDerivAt k b

/-- On the original open base, parameter differentiation commutes with the genuine coefficient. -/
theorem coefficientValue_fderiv_apply (k : d → ℤ) (z : ℂ) (hz : z ∈ U) (v : ℂ) :
    fderiv ℝ (f.coefficientValue k) z v = (f.baseDerivative v).coefficientValue k z := by
  rw [(f.coefficientValue_hasFDerivAt k ⟨z, hz⟩).fderiv,
    f.coefficientDifferential_apply k ⟨z, hz⟩ v,
    coefficientValue_apply (f.baseDerivative v) k ⟨z, hz⟩]

/-- The actual coefficient is differentiable everywhere inside the original base open. -/
theorem coefficientValue_differentiableOn (k : d → ℤ) :
    DifferentiableOn ℝ (f.coefficientValue k) U :=
  fun z hz => (f.coefficientValue_hasFDerivAt k ⟨z, hz⟩).differentiableAt.differentiableWithinAt

end SmoothFamily

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter
