import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottStabilization
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCandidateRankClass

/-!
# The explicit candidate in every larger quaternionic rank

The original literal sphere map is stabilized by the actual matrix inclusion.
Its formula is the same double Bott matrix applied to the identity-bordered
five-sphere input. The existing native stabilization isomorphism carries the
original class to precisely this class.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicColumns QuaternionicBottMatrix QuaternionicSymmetricMatrices

attribute [local irreducible] unreducedSphereCandidate symmetricMap

def stableSymmetricInput (r : ℕ) : C(UnitSphere, Space (Fin (3 + r))) :=
  (QuaternionicSymmetricMatrices.stabilizationIterate 3 r).comp symmetricMap

theorem stableSymmetricInput_axis (r : ℕ) : stableSymmetricInput r axis = identity := by
  change QuaternionicSymmetricMatrices.stabilizationIterate 3 r (symmetricMap axis) = identity
  rw [symmetricMap_axis, QuaternionicSymmetricMatrices.stabilizationIterate_identity]

theorem stableSymmetricInput_determinant (r : ℕ) (z : UnitSphere) :
    determinant (stableSymmetricInput r z) = 1 := by
  change determinant (QuaternionicSymmetricMatrices.stabilizationIterate 3 r (symmetricMap z)) = 1
  rw [QuaternionicSymmetricMatrices.stabilizationIterate_determinant]
  apply Circle.ext
  exact symmetricMap_det z

def stableSpecialInput (r : ℕ) : C(UnitSphere, SpecialSpace (Fin (3 + r))) :=
  ⟨fun z ↦ ⟨stableSymmetricInput r z, stableSymmetricInput_determinant r z⟩,
    (stableSymmetricInput r).continuous.subtype_mk _⟩

theorem stableSpecialInput_axis (r : ℕ) : stableSpecialInput r axis = specialIdentity :=
  Subtype.ext (stableSymmetricInput_axis r)

def stableSphereCandidate (r : ℕ) : C(Sphere 7, SpGroup (Fin (3 + r))) :=
  (stabilizationIterateMap 3 r).comp unreducedSphereCandidate

theorem stableSphereCandidate_sourcePoint (r : ℕ) (s t : I) (z : UnitSphere) :
    stableSphereCandidate r (sphereSourcePoint s t z) =
      twoCubeMap (stableSymmetricInput r z) ![s, t] := by
  change QuaternionicColumns.stabilizationIterate 3 r
    (unreducedSphereCandidate (sphereSourcePoint s t z)) = _
  rw [unreducedSphereCandidate_sourcePoint]
  exact (twoCubeMap_stabilizationIterate (symmetricMap z) r ![s, t]).symm

theorem stableSphereCandidate_basepoint (r : ℕ) :
    stableSphereCandidate r sphereCandidateBasepoint = 1 := by
  change QuaternionicColumns.stabilizationIterate 3 r
    (unreducedSphereCandidate sphereCandidateBasepoint) = 1
  rw [unreducedSphereCandidate_basepoint, map_one]

def stableSphereCandidateClass (r : ℕ) : π_ 7 (SpGroup (Fin (3 + r))) 1 :=
  pointedMap (stableSphereCandidate r) sphereCandidateBasepoint 1
    (stableSphereCandidate_basepoint r) (sphereSevenGenerator sphereCandidateBasepoint)

theorem stableSphereCandidateClass_eq_stabilization (r : ℕ) :
    stableSphereCandidateClass r =
      stabilizationInRangeIterate 3 7 (by decide) r unreducedSphereCandidateClass := by
  rw [stabilizationInRangeIterate_apply]
  have h := pointedMap_comp (N := Fin 7) unreducedSphereCandidate (stabilizationIterateMap 3 r)
    sphereCandidateBasepoint 1 1 unreducedSphereCandidate_basepoint
    (QuaternionicColumns.stabilizationIterate 3 r).map_one
  exact congrArg (fun f : π_ 7 (Sphere 7) sphereCandidateBasepoint →*
    π_ 7 (SpGroup (Fin (3 + r))) 1 ↦ f (sphereSevenGenerator sphereCandidateBasepoint)) h

def stableCandidateRankMulEquiv (r : ℕ) :
    π_ 7 QuaternionicFibration.SpTwo 1 ≃* π_ 7 (SpGroup (Fin (3 + r))) 1 :=
  candidateRankMulEquiv.trans (stabilizationInRangeIterate 3 7 (by decide) r)

theorem stableCandidateRankMulEquiv_candidate (r : ℕ) :
    stableCandidateRankMulEquiv r sphereCandidateClass = stableSphereCandidateClass r := by
  change stabilizationInRangeIterate 3 7 (by decide) r
    (candidateRankMulEquiv sphereCandidateClass) = _
  rw [candidateRankMulEquiv_candidate, stableSphereCandidateClass_eq_stabilization]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
