import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisMeanBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisSmooth

/-!
# The genuinely smooth mean-removed original family

The proved rapid bounds for the original Haar coefficients and the proved
smooth Fourier synthesis construct a genuine smooth family after deleting
the zero mode. Its value is the original function minus its actual Haar
mean on each fibre, and its Fourier coefficients are computed exactly.
-/

noncomputable section

open MeasureTheory TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open FourierParameter RelativeHomotopy PeriodTorusLineBundleClassification

variable {U : Opens ℂ}

/-- The original family with its actual fibrewise mean removed; its joint
smoothness follows from the proved Fourier synthesis theorem. -/
def meanRemovedFamily (f : SmoothFamily U (Fin 4)) : SmoothFamily U (Fin 4) :=
  smoothFamily (removeZeroCoefficients_rapid (smoothRapidCoefficients_actual f))

/-- The mean-removed family is the original function minus its zero coefficient. -/
theorem meanRemovedFamily_apply (f : SmoothFamily U (Fin 4))
    (b : U) (t : UnitAddTorus (Fin 4)) :
    meanRemovedFamily f (b, t) = f (b, t) - f.coefficientValue 0 (b : ℂ) := by
  change synthesis (removeZeroCoefficients f.coefficientValue) (b, t) = _
  rw [synthesis_removeZeroCoefficients (smoothRapidCoefficients_actual f),
    synthesis_coefficientValue]

/-- Pointwise, the constructed smooth family subtracts the original Haar integral. -/
theorem meanRemovedFamily_apply_eq_sub_haarIntegral (f : SmoothFamily U (Fin 4))
    (b : U) (t : UnitAddTorus (Fin 4)) :
    meanRemovedFamily f (b, t) = f (b, t) -
      ∫ s : UnitAddTorus (Fin 4), f (b, s)
        ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle) := by
  rw [meanRemovedFamily_apply, SmoothFamily.coefficientValue_apply,
    mFourierCoeff_zero_eq_haarIntegral]

/-- The actual Haar coefficients of the constructed smooth family are
precisely the original coefficients with the zero frequency removed. -/
theorem coefficientValue_meanRemovedFamily (f : SmoothFamily U (Fin 4))
    (b : U) (k : Frequency) :
    (meanRemovedFamily f).coefficientValue k (b : ℂ) =
      removeZeroCoefficients f.coefficientValue k (b : ℂ) := by
  rw [SmoothFamily.coefficientValue_apply]
  exact mFourierCoeff_synthesis
    (removeZeroCoefficients_rapid (smoothRapidCoefficients_actual f)) b k

/-- The constructed smooth family has actual Haar mean zero on every original fibre. -/
theorem meanRemovedFamily_haarIntegral (f : SmoothFamily U (Fin 4)) (b : U) :
    (∫ t : UnitAddTorus (Fin 4), meanRemovedFamily f (b, t)
      ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle)) = 0 :=
  haarIntegral_removeZeroSynthesis (smoothRapidCoefficients_actual f) b

/-- The existing smooth-torus mean of the original slice is also zero. -/
theorem torusFourierMean_meanRemovedFamily_slice (f : SmoothFamily U (Fin 4)) (b : U) :
    torusFourierMean ((meanRemovedFamily f).slice b) = 0 := by
  change mFourierCoeff (fun t => meanRemovedFamily f (b, t)) 0 = 0
  rw [mFourierCoeff_zero_eq_haarIntegral]
  exact meanRemovedFamily_haarIntegral f b

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
