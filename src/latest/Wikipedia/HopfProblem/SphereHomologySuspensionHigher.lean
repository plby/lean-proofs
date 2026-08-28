import Wikipedia.HopfProblem.SphereHomologySuspension
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionMayerVietoris

/-!
# Higher homology of the actual suspension and Euclidean spheres

The two genuine contractible cone charts and their genuine middle-band
homotopy equivalence identify suspension homology through the original
singular Mayer--Vietoris connecting map. The latitude homeomorphism then
gives the dimension-shifting map for the literal Euclidean unit spheres.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SphereHomology

open CuspCentralHomology SingularMayerVietoris PeriodTorusHigherHomology

variable (X : Type) [TopologicalSpace X] [Nonempty X]

/-- Actual suspension homology in degree `k+2`, via the actual cone-cover connecting map. -/
def suspensionHomologyHigherEquiv (k : ℕ) :
    SingularHomology (Suspension X) (k + 2) ≃ₗ[ℤ] SingularHomology X (k + 1) :=
  (contractibleCoverHomologyHigherEquiv
    Suspension.northOpen Suspension.southOpen
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover k).trans
      (homotopyEquivHomologyEquiv Suspension.middleBandHomotopyEquiv (k + 1))

/-- The suspension equivalence retains the original connecting map and overlap projection. -/
theorem suspensionHomologyHigherEquiv_apply (k : ℕ)
    (a : SingularHomology (Suspension X) (k + 2)) :
    suspensionHomologyHigherEquiv X k a =
      singularHomologyMap Suspension.middleBandHomotopyEquiv.toFun (k + 1)
        (connectingHomomorphism Suspension.northOpen Suspension.southOpen
          Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover
          (k + 1) a) := rfl

/-- The dimension shift for the original Euclidean unit spheres. -/
def unitSphereHomologySuspensionEquiv (n k : ℕ) :
    SingularHomology (UnitSphere (n + 1)) (k + 2) ≃ₗ[ℤ]
      SingularHomology (UnitSphere n) (k + 1) :=
  (homeomorphHomologyEquiv (suspensionSphereHomeomorph n).symm (k + 2)).trans
    (suspensionHomologyHigherEquiv (UnitSphere n) k)

/-- The sphere dimension shift is the actual map of the inverse latitude homeomorphism
followed by the actual singular suspension connecting map. -/
theorem unitSphereHomologySuspensionEquiv_apply (n k : ℕ)
    (a : SingularHomology (UnitSphere (n + 1)) (k + 2)) :
    unitSphereHomologySuspensionEquiv n k a =
      suspensionHomologyHigherEquiv (UnitSphere n) k
        (singularHomologyMap ((suspensionSphereHomeomorph n).symm :
          ContinuousMap (UnitSphere (n + 1)) (Suspension (UnitSphere n))) (k + 2) a) := rfl

end Wikipedia.HopfProblem.SphereHomology
