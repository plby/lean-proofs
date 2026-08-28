import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeHomotopySelection
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverseHolomorphicBasic

/-!
# The actual antiholomorphic base derivative of Fourier coefficients

The operator uses the real Fréchet derivative on the original complex
base, with the usual factor `1/2`. The rapid coefficient class is closed
under it. For a genuinely holomorphic multiplier the actual product rule
proves that this operator differentiates only the other factor.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierSynthesis FourierSynthesisInverse

/-- The actual antiholomorphic derivative on the original complex base. -/
def baseDbar (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I)

theorem baseDbar_apply (g : ℂ → ℂ) (z : ℂ) :
    baseDbar g z = (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) / 2 := by
  rw [baseDbar, div_eq_mul_inv, mul_comm]

/-- Apply the genuine base antiholomorphic derivative to each original coefficient. -/
def baseDbarCoefficients (c : Coefficients) : Coefficients := fun k => baseDbar (c k)

theorem baseDbarCoefficients_apply (c : Coefficients) (k : Frequency) (z : ℂ) :
    baseDbarCoefficients c k z =
      (fderiv ℝ (c k) z 1 + Complex.I * fderiv ℝ (c k) z Complex.I) / 2 :=
  baseDbar_apply (c k) z

/-- Actual base antiholomorphic differentiation preserves all rapid estimates. -/
theorem baseDbarCoefficients_rapid {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) : SmoothRapidCoefficients U (baseDbarCoefficients c) :=
  ((hc.baseDiff 1).add ((hc.baseDiff Complex.I).const_mul Complex.I)).const_mul (2 : ℂ)⁻¹

/-- A genuinely holomorphic scalar multiplier has zero actual antiholomorphic derivative. -/
theorem baseDbar_eq_zero_of_holomorphicAt {m : ℂ → ℂ} {z : ℂ}
    (hm : DifferentiableAt ℂ m z) : baseDbar m z = 0 := by
  rw [baseDbar, real_fderiv_apply_eq_complex_deriv hm 1,
    real_fderiv_apply_eq_complex_deriv hm Complex.I]
  calc
    (2 : ℂ)⁻¹ * (deriv m z * 1 + Complex.I * (deriv m z * Complex.I)) =
        (2 : ℂ)⁻¹ * deriv m z * (1 + Complex.I * Complex.I) := by ring
    _ = 0 := by rw [Complex.I_mul_I]; ring

/-- The genuine real product rule and scalar restriction of the complex
derivative imply commutation with a holomorphic multiplier. -/
theorem baseDbar_mul_of_holomorphicAt {m c : ℂ → ℂ} {z : ℂ}
    (hm : DifferentiableAt ℂ m z) (hc : DifferentiableAt ℝ c z) :
    baseDbar (fun w => m w * c w) z = m z * baseDbar c z := by
  have hmR : DifferentiableAt ℝ m z :=
    (hm.hasDerivAt.hasFDerivAt.restrictScalars ℝ).differentiableAt
  have hp : HasFDerivAt (fun w => m w * c w)
      (m z • fderiv ℝ c z + c z • fderiv ℝ m z) z :=
    hmR.hasFDerivAt.mul hc.hasFDerivAt
  rw [baseDbar, hp.fderiv, baseDbar]
  change (2 : ℂ)⁻¹ * ((m z * fderiv ℝ c z 1 + c z * fderiv ℝ m z 1) +
    Complex.I * (m z * fderiv ℝ c z Complex.I + c z * fderiv ℝ m z Complex.I)) = _
  rw [real_fderiv_apply_eq_complex_deriv hm 1,
    real_fderiv_apply_eq_complex_deriv hm Complex.I]
  calc
    (2 : ℂ)⁻¹ * ((m z * fderiv ℝ c z 1 + c z * (deriv m z * 1)) +
        Complex.I * (m z * fderiv ℝ c z Complex.I + c z * (deriv m z * Complex.I))) =
      m z * ((2 : ℂ)⁻¹ * (fderiv ℝ c z 1 + Complex.I * fderiv ℝ c z Complex.I)) +
        (2 : ℂ)⁻¹ * c z * deriv m z * (1 + Complex.I * Complex.I) := by ring
    _ = m z * ((2 : ℂ)⁻¹ * (fderiv ℝ c z 1 + Complex.I * fderiv ℝ c z Complex.I)) := by
      rw [Complex.I_mul_I]
      ring

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
