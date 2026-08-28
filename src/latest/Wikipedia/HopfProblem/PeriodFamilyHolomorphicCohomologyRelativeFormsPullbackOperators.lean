import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFormsPullbackFamily
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeOperatorsDifferential

/-!
# The genuine torus-family operators are the full native frame coefficients

This identifies the already constructed actual smooth-family operators
`d0`, `d1`, and `d2` with the coefficients obtained from the real chain rule.
The operators are not defined from the frame or from a replacement
differential: their literal lifted real derivatives are used in the proof.
-/

noncomputable section

open TopologicalSpace
open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback

open HolomorphicDolbeaultThree FourierParameter
open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The genuine native base operator is the actual lifted base coefficient. -/
theorem d0_apply_lift (f : SmoothFamily U (Fin 4)) (b : U) (x : RealPlane₄) :
    RelativeOperators.d0 f (b, torusQuotient x) =
      baseCoefficient (fderiv ℝ (ambientLift f) ((b : ℂ), x)) := by
  simpa only [ambientLift_apply, baseCoefficient] using
    RelativeOperators.ambientLift_d0 f ((b : ℂ), x) b.property

/-- The first genuine native relative operator has exactly the first
reduced coefficient at every real lift of the original torus point. -/
theorem d1_apply_lift (f : SmoothFamily U (Fin 4)) (b : U) (x : RealPlane₄) :
    let L := fderiv ℝ (ambientLift f) ((b : ℂ), x)
    RelativeOperators.d1 P f (b, torusQuotient x) = realCoefficient L 0 -
      (6 * (P.point b).val.μ * realCoefficient L 2 +
        (P.point b).val.β * realCoefficient L 3) := by
  simpa only [ambientLift_apply, realCoefficient, Smooth.muValue_apply,
    Smooth.betaValue_apply] using
      RelativeOperators.ambientLift_d1 P f ((b : ℂ), x) b.property

/-- The second genuine native relative operator likewise has the literal
second reduced real-coordinate coefficient. -/
theorem d2_apply_lift (f : SmoothFamily U (Fin 4)) (b : U) (x : RealPlane₄) :
    let L := fderiv ℝ (ambientLift f) ((b : ℂ), x)
    RelativeOperators.d2 P f (b, torusQuotient x) = realCoefficient L 1 -
      ((P.point b).val.τ * realCoefficient L 2 +
        (P.point b).val.μ * realCoefficient L 3) := by
  simpa only [ambientLift_apply, realCoefficient, Smooth.tauValue_apply,
    Smooth.muValue_apply] using
      RelativeOperators.ambientLift_d2 P f ((b : ℂ), x) b.property

/-- The full native antiholomorphic differential of the original upstairs
function has exactly the three actual smooth-family operator coefficients. -/
theorem familyPullback_dbar_operators (f : SmoothFamily U (Fin 4))
    (b : U) (z : ComplexPlane₂) :
    let t := torusQuotient ((P.periodEquiv b).symm z)
    dbar (familyPullback P f) ((b : ℂ), z) =
      RelativeOperators.d0 f (b, t) • baseCovector.val +
        RelativeOperators.d1 P f (b, t) • dbar (coordinate P 0) ((b : ℂ), z) +
        RelativeOperators.d2 P f (b, t) • dbar (coordinate P 1) ((b : ℂ), z) := by
  dsimp only
  rw [d0_apply_lift, d1_apply_lift, d2_apply_lift]
  exact familyPullback_dbar P f b z

/-- Uniqueness in the genuine full frame identifies its inverse with the
three original smooth-family operators, at the original torus point. -/
theorem familyPullback_frame_inverse_operators (f : SmoothFamily U (Fin 4))
    (b : U) (z : ComplexPlane₂) :
    let t := torusQuotient ((P.periodEquiv b).symm z)
    (frameEquiv P b z).symm
      ⟨dbar (familyPullback P f) ((b : ℂ), z), dbar_mem _ _⟩ =
      (RelativeOperators.d0 f (b, t),
        ![RelativeOperators.d1 P f (b, t), RelativeOperators.d2 P f (b, t)]) := by
  dsimp only
  rw [familyPullback_frame_inverse, d0_apply_lift, d1_apply_lift, d2_apply_lift]
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeForms.Pullback
