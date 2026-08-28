import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfEndpointMatrices
import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfEndpointGenerator
import Wikipedia.HomotopyGroupsOfSpheres.BalancedMatrixCoordinates

/-! # The actual Hopf-frame endpoint is the realification of the explicit SU(2) block -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open BalancedRealInvolutions

theorem canonicalHopfEndpoint_operator (q : EquatorSphere) :
    canonicalPoleFrame.val.adjoint.comp
      ((matrixOrthogonal (correctedRawHopfRotation q Real.pi)).val.val.comp
        canonicalPoleFrame.val) = (boundaryOrthogonal q).val.val := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 6) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro i
  change (canonicalPoleFrame.val.adjoint
    ((matrixOrthogonal (correctedRawHopfRotation q Real.pi)).val.val
      (canonicalPoleFrame.val (EuclideanSpace.basisFun (Fin 6) ℝ j)))) i =
    (matrixOrthogonal (ComplexMatrixRealification.unitaryMap (boundaryPaddedUnitary q))).val.val
      (EuclideanSpace.basisFun (Fin 6) ℝ j) i
  rw [canonicalPoleFrame_adjoint_apply, canonicalPoleFrame_basis,
    matrixOrthogonal_basis, matrixOrthogonal_basis]
  exact correctedRawHopfRotation_positive_coordinates q i j

def boundaryMap : C(EquatorSphere, OrthogonalOperators 6) :=
  ⟨boundaryOrthogonal, continuous_boundaryOrthogonal⟩

def boundaryCube (p : GenLoop (Fin 3) EquatorSphere equatorPole) :
    GenLoop (Fin 3) (OrthogonalOperators 6) 1 where
  val := boundaryMap.comp p.val
  property u hu := by
    change boundaryOrthogonal (p u) = 1
    have hpoint : p u = equatorPole := p.property u hu
    rw [hpoint, boundaryOrthogonal_equatorPole]

theorem canonicalHopfFrameLift_endpoint (p : GenLoop (Fin 3) EquatorSphere equatorPole) :
    (hopfFrameLift canonicalPoleFrame canonicalPoleFrame_project p).endpoint =
      boundaryCube p := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  apply Subtype.ext
  exact (hopfFrameLift_endpoint_operator canonicalPoleFrame canonicalPoleFrame_project p u).trans
    (canonicalHopfEndpoint_operator (p u))

def boundaryInputClass : π_ 3 (OrthogonalOperators 6) 1 :=
  ⟦boundaryCube parameterThreeCube⟧

theorem hopfEndpointClass_canonical :
    hopfEndpointClass canonicalPoleFrame canonicalPoleFrame_project = boundaryInputClass :=
  congrArg (fun p : GenLoop (Fin 3) (OrthogonalOperators 6) 1 ↦
    (⟦p⟧ : π_ 3 (OrthogonalOperators 6) 1))
    (canonicalHopfFrameLift_endpoint parameterThreeCube)

theorem sphereCandidate_generates_iff_boundary :
    Function.Surjective (fun k : ℤ ↦ ComplexCrossProductUnitary.sphereCandidateClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ boundaryInputClass ^ k) := by
  have h := sphereCandidate_generates_iff_hopfEndpoint
    canonicalPoleFrame canonicalPoleFrame_project
  rw [hopfEndpointClass_canonical] at h
  exact h

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
