import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverseApplicationFamily

/-!
# The inverse-mode operator on a genuine jointly smooth family

The input is an actual smooth function on the original base and unit
torus. Its coefficient regularity and decay are the previously proved
consequences of joint smoothness and actual Haar differentiation, not
additional assumptions. Applying the original inverse to those genuine
Fourier coefficients gives the actual jointly smooth inverse-mode series.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse

open FourierSynthesis PeriodTorusLineBundleClassification

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U) (b₀ : U)
variable {V : Opens ℂ} (hVU : V ≤ U)
variable (hm : SmoothPolynomiallyBoundedCoefficients V
  (RelativeFourier.ambientInverse P (P.point b₀)))

/-- Apply the genuine original inverse modes to the actual Haar coefficients.
The needed rapid coefficient property is derived from the given smooth family. -/
def inverseFourierFamily (f : FourierParameter.SmoothFamily U (Fin 4)) :
    FourierParameter.SmoothFamily V (Fin 4) :=
  inverseSmoothFamily P b₀ hVU hm (smoothRapidCoefficients_actual f)

/-- Literal Fourier-series values, with the actual Haar coefficients of the input slice. -/
theorem inverseFourierFamily_apply (f : FourierParameter.SmoothFamily U (Fin 4))
    (b : V) (t : UnitAddTorus (Fin 4)) :
    inverseFourierFamily P b₀ hVU hm f (b, t) =
      ∑' k, (RelativeFourier.ambientInverse P (P.point b₀) k (b : ℂ) *
        mFourierCoeff (fun q => f (Set.inclusion hVU b, q)) k) * mFourier k t := by
  change inverseSmoothFamily P b₀ hVU hm (smoothRapidCoefficients_actual f) (b, t) = _
  rw [inverseSmoothFamily_apply]
  apply tsum_congr
  intro k
  rw [f.coefficientValue_apply k (Set.inclusion hVU b)]

/-- Both the inverse and the input coefficient are their original native family values. -/
theorem inverseFourierFamily_apply_native (f : FourierParameter.SmoothFamily U (Fin 4))
    (b : V) (t : UnitAddTorus (Fin 4)) :
    inverseFourierFamily P b₀ hVU hm f (b, t) =
      ∑' k, (RelativeFourier.denominatorInverse (P.point b₀)
        (P.point (Set.inclusion hVU b)) (integerFrequency k) *
          mFourierCoeff (fun q => f (Set.inclusion hVU b, q)) k) * mFourier k t := by
  rw [inverseFourierFamily_apply]
  apply tsum_congr
  intro k
  rw [RelativeFourier.ambientInverse_apply P (P.point b₀) k (Set.inclusion hVU b)]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse
