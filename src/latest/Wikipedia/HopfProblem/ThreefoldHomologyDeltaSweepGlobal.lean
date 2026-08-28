import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepAction
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepGeneral
import Wikipedia.HopfProblem.ThreefoldHomologyLowDegrees

/-!
# The genuine global delta sweep vanishes on first homology

The operation is defined by the actual positive-circle cross product
followed by the homology map of the original global circle action. Its
degree-one vanishing then follows from the previously proved first
Hurewicz calculation of the original threefold, not from any assumed
higher homology calculation or duality theorem.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open SingularMayerVietoris PeriodTorusHigherHomology

/-- Sweep by the original global delta action, with the positive
period-one circle as the first cross-product factor. -/
def globalSweep (n : ℕ) :
    SingularHomology Space n →ₗ[ℤ] SingularHomology Space (n + 1) :=
  sweep actionMap n

@[simp] theorem globalSweep_apply (n : ℕ) (a : SingularHomology Space n) :
    globalSweep n a =
      singularHomologyMap actionMap (n + 1) (positiveCircleCross Space n a) := rfl

/-- This actual sweep, rather than a map defined to be zero, vanishes
on every genuine global first-homology class. -/
theorem globalSweep_one_apply_eq_zero (a : SingularHomology Space 1) :
    globalSweep 1 a = 0 := by
  rw [Threefold.LowDegrees.singularH1_eq_zero a, map_zero]

/-- The global operation requested in degree one is the zero integral
linear map, by the actual `H₁(X)=0` theorem. -/
theorem globalSweep_one_eq_zero : globalSweep 1 = 0 := by
  ext a
  exact globalSweep_one_apply_eq_zero a

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
