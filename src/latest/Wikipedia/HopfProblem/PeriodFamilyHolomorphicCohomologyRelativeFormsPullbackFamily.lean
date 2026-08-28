import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsPullbackFormula
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsPullbackFamilyBasic

/-!
# Actual full derivative formula for a genuine smooth torus family

There is no derivative premise in these family statements: smoothness is
the genuine lifted smoothness of the original torus family. All displayed
derivatives are those of its actual original ambient lift, evaluated at
the original inverse real period coordinates.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff ComplexConjugate

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback

open Complex HolomorphicDolbeaultThree FourierParameter

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- Full native antiholomorphic differentiation of the literal original
upstairs torus-family function, with no additional regularity hypothesis. -/
theorem familyPullback_dbar (f : SmoothFamily U (Fin 4)) (b : U) (z : ComplexPlane₂) :
    let L := fderiv ℝ (ambientLift f) ((b : ℂ), (P.periodEquiv b).symm z)
    dbar (familyPullback P f) ((b : ℂ), z) = baseCoefficient L • baseCovector.val +
      (realCoefficient L 0 -
        (6 * (P.point b).val.μ * realCoefficient L 2 +
          (P.point b).val.β * realCoefficient L 3)) •
            dbar (coordinate P 0) ((b : ℂ), z) +
      (realCoefficient L 1 -
        ((P.point b).val.τ * realCoefficient L 2 +
          (P.point b).val.μ * realCoefficient L 3)) •
            dbar (coordinate P 1) ((b : ℂ), z) :=
  ambientPullback_dbar_at P f.smooth_lift b z

/-- The literal directional formula displays exactly the real base
antiholomorphic derivative and the two reduced real-coordinate derivatives. -/
theorem familyPullback_dbar_explicit (f : SmoothFamily U (Fin 4))
    (b : U) (z : ComplexPlane₂) (v : Model) :
    let L := fderiv ℝ (ambientLift f) ((b : ℂ), (P.periodEquiv b).symm z)
    dbar (familyPullback P f) ((b : ℂ), z) v =
      ((L (1, 0) + I * L (I, 0)) / 2) * conj v.1 +
      (L (0, Pi.single 0 1) - 6 * (P.point b).val.μ * L (0, Pi.single 2 1) -
        (P.point b).val.β * L (0, Pi.single 3 1)) *
          dbar (coordinate P 0) ((b : ℂ), z) v +
      (L (0, Pi.single 1 1) - (P.point b).val.τ * L (0, Pi.single 2 1) -
        (P.point b).val.μ * L (0, Pi.single 3 1)) *
          dbar (coordinate P 1) ((b : ℂ), z) v := by
  dsimp only
  rw [familyPullback_dbar]
  simp only [add_apply, smul_apply, smul_eq_mul, baseCovector_apply,
    baseCoefficient, realCoefficient]
  ring

/-- The same explicit coefficients are the inverse of the already proved
genuine covector frame on the original covering model. -/
theorem familyPullback_frame_inverse (f : SmoothFamily U (Fin 4))
    (b : U) (z : ComplexPlane₂) :
    (frameEquiv P b z).symm
      ⟨dbar (familyPullback P f) ((b : ℂ), z), dbar_mem _ _⟩ =
      reducedCoefficients (P.point b).val.τ (P.point b).val.μ (P.point b).val.β
        (fderiv ℝ (ambientLift f) ((b : ℂ), (P.periodEquiv b).symm z)) :=
  ambientPullback_frame_inverse P f.smooth_lift b z

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback
