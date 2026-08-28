import Wikipedia.HopfProblem.SphereHomologyCircleGeometry
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The actual singular-homology map of the Euclidean-circle homeomorphism

The comparison is induced by the constructed map on the original spaces.
Its inverse is the singular-homology map induced by the actual inverse
homeomorphism, in every degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SphereHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- Path connectedness is transported through the actual Euclidean-circle homeomorphism. -/
instance sphereCircle_pathConnectedSpace :
    PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
  sphereCircleHomeomorph.symm.surjective.pathConnectedSpace
    sphereCircleHomeomorph.symm.continuous

/-- The genuine induced map on native integral singular homology in every degree. -/
def sphereCircleHomologyEquiv (n : ℕ) :
    SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n ≃ₗ[ℤ]
      SingularHomology _root_.Circle n :=
  homeomorphHomologyEquiv sphereCircleHomeomorph n

@[simp] theorem sphereCircleHomologyEquiv_toLinearMap (n : ℕ) :
    (sphereCircleHomologyEquiv n).toLinearMap =
      singularHomologyMap (sphereCircleHomeomorph :
        C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, _root_.Circle)) n := rfl

@[simp] theorem sphereCircleHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) n) :
    sphereCircleHomologyEquiv n a =
      singularHomologyMap (sphereCircleHomeomorph :
        C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, _root_.Circle)) n a := rfl

@[simp] theorem sphereCircleHomologyEquiv_symm_apply (n : ℕ)
    (a : SingularHomology _root_.Circle n) :
    (sphereCircleHomologyEquiv n).symm a =
      singularHomologyMap (sphereCircleHomeomorph.symm :
        C(_root_.Circle, Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) n a := rfl

end Wikipedia.HopfProblem.SphereHomology
