import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverseApplicationBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsProduct
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisSmooth

/-!
# Actual smooth synthesis after multiplication by the original inverse

On a neighborhood where the proved original inverse multiplier condition
holds, multiply the unchanged input coefficient functions by that inverse.
The proved rapid-product theorem and genuine Fourier-synthesis theorem
construct a jointly smooth family on the original unit torus. Its value
is the literal inverse-mode Fourier series, also expressed with the native
period-family inverse instead of its ambient representative.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse

open FourierSynthesis PeriodTorusLineBundleClassification

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U) (b₀ : U)
variable {V : Opens ℂ} (hVU : V ≤ U)
variable (hm : SmoothPolynomiallyBoundedCoefficients V
  (RelativeFourier.ambientInverse P (P.point b₀)))
variable {c : Coefficients} (hc : SmoothRapidCoefficients U c)

/-- The literal original inverse-mode series as a genuinely jointly smooth family. -/
def inverseSmoothFamily : FourierParameter.SmoothFamily V (Fin 4) :=
  FourierSynthesis.smoothFamily (hm.mul_rapid (hc.mono hVU))

@[simp] theorem inverseSmoothFamily_apply (b : V) (t : UnitAddTorus (Fin 4)) :
    inverseSmoothFamily P b₀ hVU hm hc (b, t) =
      ∑' k, (RelativeFourier.ambientInverse P (P.point b₀) k (b : ℂ) * c k (b : ℂ)) *
        mFourier k t := rfl

/-- The same series uses the actual inverse at the original period-map point.
Only the inclusion of the proved smaller open into the original base is used. -/
theorem inverseSmoothFamily_apply_native (b : V) (t : UnitAddTorus (Fin 4)) :
    inverseSmoothFamily P b₀ hVU hm hc (b, t) =
      ∑' k, (RelativeFourier.denominatorInverse (P.point b₀)
        (P.point (Set.inclusion hVU b)) (integerFrequency k) * c k (b : ℂ)) *
          mFourier k t := by
  rw [inverseSmoothFamily_apply]
  apply tsum_congr
  intro k
  rw [RelativeFourier.ambientInverse_apply P (P.point b₀) k (Set.inclusion hVU b)]

/-- The genuine quotient family has the literal Fourier sum on its original real cover. -/
theorem ambientLift_inverseSmoothFamily (b : V) (x : Fin 4 → ℝ) :
    FourierParameter.ambientLift (inverseSmoothFamily P b₀ hVU hm hc)
        ((b : ℂ), x) =
      ∑' k, (RelativeFourier.ambientInverse P (P.point b₀) k (b : ℂ) * c k (b : ℂ)) *
        mFourier k (torusQuotient x) := by
  rw [FourierParameter.ambientLift_apply]
  exact inverseSmoothFamily_apply P b₀ hVU hm hc b (torusQuotient x)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse
