import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSpherePreimages
import Wikipedia.HomotopyGroupsOfSpheres.ProjectedSphereDegree

/-! # The global candidate defines an actual native class with its actual projected degree -/

noncomputable section

open scoped Topology unitInterval Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicFibration
open Wikipedia.HopfProblem.SphereHomology

def sphereCandidateBasepoint : Sphere 7 := sphereSourcePoint 0 0 axis

theorem sphereCandidateBasepoint_image : sphereCandidate sphereCandidateBasepoint = 1 :=
  sphereCandidate_outer_zero (Latitude.point 5 0 (sphereFiveHomeomorph.symm axis))

def sphereCandidateClass : π_ 7 SpTwo 1 :=
  pointedMap sphereCandidate sphereCandidateBasepoint 1 sphereCandidateBasepoint_image
    (sphereSevenGenerator sphereCandidateBasepoint)

def sphereCandidateDegreeMap : C(Sphere 7, Sphere 7) := projectedSphereMap sphereCandidate

theorem sphereCandidateClass_projectionDegree :
    (projectionDegree sphereCandidateClass).toAdd = sphereSevenDegree sphereCandidateDegreeMap :=
  projectionDegree_pointed_sphereMap sphereCandidate sphereCandidateBasepoint
    sphereCandidateBasepoint_image

/-- The global map retains the exact matrix formula of the previously constructed native cubes. -/
theorem sphereCandidate_reducedSevenCubeSum (p : GenLoop (Fin 5) UnitSphere axis)
    (u : Fin 5 → I) (v : Fin 2 → I) :
    sphereCandidate (sphereSourcePoint (v 0) (v 1) (p u)) =
      reducedSevenCubeSum p (Sum.elim u v) := by
  rw [sphereCandidate_sourcePoint, reducedSevenCubeSum_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
