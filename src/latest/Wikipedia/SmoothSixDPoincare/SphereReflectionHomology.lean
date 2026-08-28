import Wikipedia.SmoothSixDPoincare.SphereReflection
import Wikipedia.SmoothSixDPoincare.SuspensionReflectionHomology

/-!
# The actual Euclidean reflection acts by minus one on sphere homology

Conjugate the literal height reflection through the proved latitude
homeomorphism. This computes the induced map without choosing a generator.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare.SphereReflection

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

theorem sphereMap_homology (n k : ℕ) (a : SingularHomology (UnitSphere (n + 1)) (k + 1)) :
    singularHomologyMap (sphereMap n) (k + 1) a = -a := by
  obtain ⟨b, rfl⟩ := (homotopyEquivHomologyEquiv
    (suspensionSphereHomeomorph n).toHomotopyEquiv (k + 1)).surjective a
  change singularHomologyMap (sphereMap n) (k + 1)
    (singularHomologyMap (suspensionSphereHomeomorph n).toHomotopyEquiv.toFun (k + 1) b) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, sphereMap_comp_suspension,
    singularHomologyMap_comp, LinearMap.comp_apply, SuspensionReflection.reflect_homology,
    map_neg]
  rfl

end Wikipedia.SmoothSixDPoincare.SphereReflection
