import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisModesBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsBasic

/-!
# Original joint Fourier derivatives in the smooth rapid coefficient class

The literal mode derivative has exactly the coefficient obtained by
the actual base directional derivative and the actual frequency
multipliers. The smoothness hypothesis on each original coefficient
supplies its derivative on the original open base.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open PeriodTorusLineBundleClassification

/-- Every original mode is differentiable at every point over the
original base, with the previously computed actual joint derivative. -/
theorem hasFDerivAt_jointFourierMode_of_smoothRapid {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) (k : Frequency) (x : ℂ × (Fin 4 → ℝ))
    (hx : x.1 ∈ U) :
    HasFDerivAt (jointFourierMode c k) (jointFourierModeDerivative c k x) x :=
  hasFDerivAt_jointFourierMode c k x
    (((hc.smooth k).contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt (by simp))

/-- The joint derivative retains the exact original Fourier character
and the proved real directional/frequency coefficient formula. -/
theorem jointFourierModeDerivative_apply_coefficients (c : Coefficients) (k : Frequency)
    (x v : ℂ × (Fin 4 → ℝ)) :
    jointFourierModeDerivative c k x v =
      jointDerivativeCoefficients v c k x.1 * mFourier k (torusQuotient x.2) := by
  have h : fderiv ℝ (c k) x.1 v.1 +
      (∑ j : Fin 4, (2 * (Real.pi : ℂ) * Complex.I * (k j : ℂ)) *
        (v.2 j : ℂ) * c k x.1) = jointDerivativeCoefficients v c k x.1 := by
    rw [jointDerivativeCoefficients_apply, baseDiff_apply]
    apply congrArg (fun a : ℂ => fderiv ℝ (c k) x.1 v.1 + a)
    apply Finset.sum_congr rfl
    intro j _
    rw [frequencyDiff_apply]
    ring
  exact (jointFourierModeDerivative_apply c k x v).trans
    (congrArg (fun a : ℂ => a * mFourier k (torusQuotient x.2)) h)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
