import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsProductMajorant

/-!
# Smooth rapid coefficients multiplied by a smooth polynomial family

Actual real smoothness and the proved finite-word Leibniz estimates show
that a smooth multiplier with compact-polynomial bounds for all its
original base-derivative words preserves the rapid coefficient class.
This is a coefficient theorem; it asserts no infinite-series regularity
or relative cohomology comparison.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

variable {U : Opens ℂ} {m c : Coefficients}

/-- Left multiplication by a smooth compact-polynomial family preserves
the actual smooth rapidly decreasing coefficient condition. -/
theorem SmoothPolynomiallyBoundedCoefficients.mul_rapid
    (hm : SmoothPolynomiallyBoundedCoefficients U m) (hc : SmoothRapidCoefficients U c) :
    SmoothRapidCoefficients U (fun k z => m k z * c k z) where
  smooth k := (hm.smooth k).mul (hc.smooth k)
  majorant s K hK r := polynomial_mul_rapid_majorant s m c hm hc K hK r

/-- Right multiplication by a smooth compact-polynomial family preserves
the actual smooth rapidly decreasing coefficient condition. -/
theorem SmoothRapidCoefficients.mul (hc : SmoothRapidCoefficients U c)
    (hm : SmoothPolynomiallyBoundedCoefficients U m) :
    SmoothRapidCoefficients U (fun k z => c k z * m k z) := by
  have heq : (fun k z => m k z * c k z) = (fun k z => c k z * m k z) :=
    funext (fun _ => funext (fun _ => mul_comm _ _))
  exact heq ▸ hm.mul_rapid hc

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
