import Wikipedia.HopfProblem.ConifoldPolarBasic
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealFourCircleParameter
import Wikipedia.HopfProblem.StandardSixSphereCircleModelIsometries

/-!
# The original period-one circle and the standard six-sphere complement

The normal rotation in polar coordinates is exactly the already-defined native
real-four rotation.  Composing the two explicit standard-model homeomorphisms
identifies the determinant-one smoothing with the standard six-sphere minus
its equatorial two-sphere.  This is not a map from the constructed threefold.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConifoldPolar

open CuspCircleNormalTrivialization
open SpecialPeriods.Threefold.Homology
open SpecialPeriods.Threefold.VerticalAction.FixedCoordinates

theorem normalRotation_eq_native (u : ℂ) (z : Normal) :
    normalRotation u z = RealFour.rotationMap u z := rfl

theorem sphereRotation_eq_native (u : ℂˣ) (hu : ‖(u : ℂ)‖ = 1) (z : NormalSphere) :
    sphereRotation (u : ℂ) hu z =
      StandardSixSphereCircleModel.Isometries.normalSphereMap (RealFour.rotation u hu) z := rfl

/-- The original delta-circle parameter, with its original period and sign. -/
def periodCircleAction (t : AddCircle (1 : ℝ)) (M : SpecialLinear) : SpecialLinear :=
  circleAction (DeltaSweep.circleParameter t : ℂ) (CircleOrbit.circleParameter_norm t) M

/-- Exact equivariance with the previously formalized native circle rotation. -/
theorem homeomorph_periodCircleAction (t : AddCircle (1 : ℝ)) (M : SpecialLinear) :
    homeomorph (periodCircleAction t M) =
      ((homeomorph M).1, StandardSixSphereCircleModel.Isometries.normalSphereMap
        (RealFour.circleRotation t) (homeomorph M).2) :=
  homeomorph_circleAction (DeltaSweep.circleParameter t : ℂ)
    (CircleOrbit.circleParameter_norm t) M

/-- Explicit standard-model identification with the original equator complement in `S⁶`. -/
def standardComplementHomeomorph : SpecialLinear ≃ₜ StandardSixSphereCircleModel.Complement :=
  homeomorph.trans StandardSixSphereCircleModel.homeomorph.symm

@[simp] theorem standardComplementHomeomorph_apply (M : SpecialLinear) :
    standardComplementHomeomorph M = StandardSixSphereCircleModel.inverse (forward M) := rfl

@[simp] theorem standardComplementHomeomorph_symm_apply
    (p : StandardSixSphereCircleModel.Complement) :
    standardComplementHomeomorph.symm p = inverse (StandardSixSphereCircleModel.forward p) := rfl

/-- The standard-complement identification intertwines the literal norm-one matrix action. -/
theorem standardComplementHomeomorph_circleAction (u : ℂˣ)
    (hu : ‖(u : ℂ)‖ = 1) (M : SpecialLinear) :
    standardComplementHomeomorph (circleAction (u : ℂ) hu M) =
      StandardSixSphereCircleModel.Isometries.complementMap (RealFour.rotation u hu)
        (standardComplementHomeomorph M) := by
  rw [standardComplementHomeomorph_apply, forward_circleAction]
  exact (StandardSixSphereCircleModel.Isometries.inverse_equivariant
    (RealFour.rotation u hu) (forward M)).symm

/-- In particular, the original period-one delta circle has its unchanged native action. -/
theorem standardComplementHomeomorph_periodCircleAction
    (t : AddCircle (1 : ℝ)) (M : SpecialLinear) :
    standardComplementHomeomorph (periodCircleAction t M) =
      StandardSixSphereCircleModel.Isometries.complementMap (RealFour.circleRotation t)
        (standardComplementHomeomorph M) :=
  standardComplementHomeomorph_circleAction (DeltaSweep.circleParameter t)
    (CircleOrbit.circleParameter_norm t) M

end Wikipedia.HopfProblem.ConifoldPolar
