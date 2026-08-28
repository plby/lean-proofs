import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCandidateDegreeTransport
import Wikipedia.HomotopyGroupsOfSpheres.SphereSevenDegreeMagnitude

/-!
# The explicit quaternionic candidate has projected degree of absolute value twelve

This computes the degree of the actual constructed class. It does not identify
that class with a generator of the seventh homotopy group of `Sp(2)`.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

theorem sphereCandidateDegree_natAbs :
    Int.natAbs (sphereSevenDegree sphereCandidateDegreeMap) = 12 :=
  sphereSevenDegree_natAbs_of_homology_smul sphereCandidateDegreeMap 12
    MidpointSeed.degreeHomologyAutomorphism
    MidpointSeed.sphereCandidateDegreeMap_homology_twelve

theorem sphereCandidateClass_projectionDegree_natAbs :
    Int.natAbs (QuaternionicFibration.projectionDegree sphereCandidateClass).toAdd = 12 := by
  rw [sphereCandidateClass_projectionDegree]
  exact sphereCandidateDegree_natAbs

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
