import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSphereRankHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.PointedMapHomotopies
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicStableRange

/-!
# The actual candidate class agrees with the unreduced class under rank stability

The isomorphism includes the explicit conjugation from the proved relative
homotopy. Thus reducing the matrix rank neither multiplies the class by an
unknown integer nor loses its generator property.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicColumns QuaternionicBottMatrix

attribute [local irreducible] sphereCandidate unreducedSphereCandidate

theorem unreducedSphereCandidate_basepoint :
    unreducedSphereCandidate sphereCandidateBasepoint = 1 := by
  rw [sphereCandidateBasepoint, unreducedSphereCandidate_sourcePoint]
  exact twoCubeFamily_boundary _ _ ⟨0, Or.inl rfl⟩

def unreducedSphereCandidateClass : π_ 7 (SpGroup (Fin 3)) 1 :=
  pointedMap unreducedSphereCandidate sphereCandidateBasepoint 1
    unreducedSphereCandidate_basepoint (sphereSevenGenerator sphereCandidateBasepoint)

def swapConjugationPiSeven : π_ 7 (SpGroup (Fin 3)) 1 ≃* π_ 7 (SpGroup (Fin 3)) 1 :=
  pointedHomeomorphMulEquiv swapConjugation 1 1 swapConjugation_one

theorem stabilization_sphereCandidateClass :
    stabilizationMap 2 7 sphereCandidateClass =
      swapConjugationPiSeven unreducedSphereCandidateClass := by
  have hc := pointedMap_eq_of_homotopyRel (N := Fin 7)
    ((swapConjugation : C(SpGroup (Fin 3), SpGroup (Fin 3))).comp unreducedSphereCandidate)
    (stabilizationContinuousMap.comp sphereCandidate) sphereCandidateBasepoint 1
    ((congrArg swapConjugation unreducedSphereCandidate_basepoint).trans swapConjugation_one)
    ((congrArg stabilizationContinuousMap sphereCandidateBasepoint_image).trans
      (stabilization 2).map_one) sphereRankHomotopyRel
  rw [pointedMap_comp unreducedSphereCandidate
      (swapConjugation : C(SpGroup (Fin 3), SpGroup (Fin 3))) sphereCandidateBasepoint 1 1
      unreducedSphereCandidate_basepoint swapConjugation_one,
    pointedMap_comp sphereCandidate stabilizationContinuousMap sphereCandidateBasepoint 1 1
      sphereCandidateBasepoint_image (stabilization 2).map_one] at hc
  have he := congrArg
    (fun f : π_ 7 (Sphere 7) sphereCandidateBasepoint →* π_ 7 (SpGroup (Fin 3)) 1 ↦
      f (sphereSevenGenerator sphereCandidateBasepoint)) hc
  change pointedMap (swapConjugation : C(SpGroup (Fin 3), SpGroup (Fin 3))) 1 1 swapConjugation_one
    unreducedSphereCandidateClass = stabilizationMap 2 7 sphereCandidateClass at he
  exact he.symm

def candidateRankMulEquiv :
    π_ 7 QuaternionicFibration.SpTwo 1 ≃* π_ 7 (SpGroup (Fin 3)) 1 :=
  (stabilizationPiSevenMulEquiv 2 (by decide)).trans swapConjugationPiSeven.symm

theorem candidateRankMulEquiv_candidate :
    candidateRankMulEquiv sphereCandidateClass = unreducedSphereCandidateClass := by
  change swapConjugationPiSeven.symm
    (stabilizationPiSevenMulEquiv 2 (by decide) sphereCandidateClass) = _
  rw [stabilizationPiSevenMulEquiv_apply, stabilization_sphereCandidateClass,
    MulEquiv.symm_apply_apply]

theorem sphereCandidate_generates_iff_unreduced :
    Function.Surjective (fun k : ℤ ↦ sphereCandidateClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ unreducedSphereCandidateClass ^ k) := by
  constructor
  · intro h a
    obtain ⟨k, hk⟩ := h (candidateRankMulEquiv.symm a)
    refine ⟨k, ?_⟩
    change unreducedSphereCandidateClass ^ k = a
    change sphereCandidateClass ^ k = candidateRankMulEquiv.symm a at hk
    rw [← candidateRankMulEquiv_candidate, ← map_zpow, hk, MulEquiv.apply_symm_apply]
  · intro h a
    obtain ⟨k, hk⟩ := h (candidateRankMulEquiv a)
    refine ⟨k, candidateRankMulEquiv.injective ?_⟩
    change candidateRankMulEquiv (sphereCandidateClass ^ k) = candidateRankMulEquiv a
    rw [map_zpow, candidateRankMulEquiv_candidate]
    exact hk

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
