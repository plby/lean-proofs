import Wikipedia.HopfProblem.CuspCentralHomologySuspensionTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePointClass

/-!
# Connectedness and actual degree-zero markings for the suspension cover

The middle band is the original overlap of the two open cones. Its
proved homeomorphism with `(1/4,3/4) × X` supplies connectedness when `X`
is path connected. The homology marking uses the actual band homotopy
equivalence, and agrees with the native singular augmentation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SphereHomology

open CuspCentralHomology SingularMayerVietoris PeriodTorusHigherHomology

variable (X : Type) [TopologicalSpace X]

section Nonempty

variable [Nonempty X]

/-- Suspending any nonempty space gives the actual degree-zero augmentation isomorphism. -/
def suspensionHomologyZeroEquivOfNonempty : SingularHomology (Suspension X) 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv (Suspension X)

@[simp] theorem suspensionHomologyZeroEquivOfNonempty_pointClass (x : Suspension X) :
    suspensionHomologyZeroEquivOfNonempty X (pointClass x) = 1 :=
  connectedHomologyZeroEquiv_pointClass x

end Nonempty

section Connected

variable [PathConnectedSpace X]

/-- The original middle band is path connected through its actual product homeomorphism. -/
instance suspension_middleBand_pathConnectedSpace :
    PathConnectedSpace (Suspension.middleBand X) :=
  (Suspension.middleBandHomeomorph (X := X)).symm.surjective.pathConnectedSpace
    (Suspension.middleBandHomeomorph (X := X)).symm.continuous

/-- Degree zero is marked through the genuine middle-band homotopy equivalence. -/
def suspensionMiddleBandHomologyZeroEquiv :
    SingularHomology (Suspension.middleBand X) 0 ≃ₗ[ℤ] ℤ :=
  (homotopyEquivHomologyEquiv (Suspension.middleBandHomotopyEquiv (X := X)) 0).trans
    (connectedHomologyZeroEquiv X)

/-- The actual induced homology map, not an assigned coordinate, defines this marking. -/
theorem suspensionMiddleBandHomologyZeroEquiv_apply
    (a : SingularHomology (Suspension.middleBand X) 0) :
    suspensionMiddleBandHomologyZeroEquiv X a =
      connectedHomologyZeroEquiv X
        (singularHomologyMap (Suspension.middleBandHomotopyEquiv (X := X)).toFun 0 a) := rfl

/-- The homotopy-equivalence marking is exactly the original augmentation of the band. -/
theorem suspensionMiddleBandHomologyZeroEquiv_eq_connectedHomologyZeroEquiv :
    suspensionMiddleBandHomologyZeroEquiv X =
      connectedHomologyZeroEquiv (Suspension.middleBand X) := by
  apply LinearEquiv.ext
  intro a
  exact connectedHomologyZeroEquiv_natural
    (Suspension.middleBandHomotopyEquiv (X := X)).toFun a

end Connected

end Wikipedia.HopfProblem.SphereHomology
