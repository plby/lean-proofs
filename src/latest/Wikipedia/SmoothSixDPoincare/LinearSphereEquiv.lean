import Wikipedia.SmoothSixDPoincare.LinearSphereComposition
import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundaryHomology

/-!
# The actual normalized invertible linear map is a homotopy equivalence

Compose the punctured linear homeomorphism with the original radial sphere
equivalences. Its forward map is exactly the normalized linear map used in
the local-boundary and global signed-count formulas.
-/

noncomputable section

open Set Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.LinearSphereAction

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E ≃L[ℝ] F)

def sphereHomotopyEquiv : sphere (0 : E) 1 ≃ₕ sphere (0 : F) 1 :=
  (LocalDegree.linearSphereEquiv B 1 zero_lt_one).trans
    (PuncturedRadial.sphereHomotopyEquiv 1 zero_lt_one).symm

theorem sphereHomotopyEquiv_toFun :
    (sphereHomotopyEquiv B).toFun = sphereMap B.toContinuousLinearMap B.injective :=
  normalized_linearSphereMap B 1 zero_lt_one

def homologyEquiv (k : ℕ) :
    SingularHomology (sphere (0 : E) 1) k ≃ₗ[ℤ]
      SingularHomology (sphere (0 : F) 1) k :=
  homotopyEquivHomologyEquiv (sphereHomotopyEquiv B) k

theorem homologyEquiv_apply (k : ℕ) (a : SingularHomology (sphere (0 : E) 1) k) :
    homologyEquiv B k a =
      singularHomologyMap (sphereMap B.toContinuousLinearMap B.injective) k a := by
  change singularHomologyMap (sphereHomotopyEquiv B).toFun k a = _
  rw [sphereHomotopyEquiv_toFun]

end Wikipedia.SmoothSixDPoincare.LinearSphereAction
