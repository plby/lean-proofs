import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfLatitudeGenerator
import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameStableRange
import Wikipedia.HomotopyGroupsOfSpheres.PointedBasepointCube

/-! # Generation reduces to the actual endpoint of the explicit Hopf frame lift -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open BalancedRealInvolutions

variable (A : Stiefel.Space 12 6) (hA : FrameProjection.toBalanced A = rawBalanced pole)

def hopfEndpointClass : π_ 3 (OrthogonalOperators 6) 1 :=
  ⟦(hopfFrameLift A hA parameterThreeCube).endpoint⟧

def hopfFrameConnectingMulEquiv :
    π_ 4 (Space 6) (rawBalanced pole) ≃* π_ 3 (OrthogonalOperators 6) 1 :=
  (basepointEqMulEquiv hA.symm).trans (FrameProjection.connectingMulEquiv A 3 (by decide))

theorem hopfFrameConnectingMulEquiv_latitude :
    hopfFrameConnectingMulEquiv A hA hopfLatitudeInputClass = hopfEndpointClass A hA := by
  have h₁ : basepointEqMulEquiv hA.symm hopfLatitudeInputClass =
      (⟦hopfLatitudeCubeAt A hA parameterThreeCube⟧ :
        π_ 4 (Space 6) (FrameProjection.toBalanced A)) :=
    basepointEqMulEquiv_mk hA.symm (hopfLatitudeCube parameterThreeCube)
  change FrameProjection.connectingMulEquiv A 3 (by decide)
    (basepointEqMulEquiv hA.symm hopfLatitudeInputClass) = _
  exact (congrArg (FrameProjection.connectingMulEquiv A 3 (by decide)) h₁).trans
    (hopfLatitude_connecting A hA parameterThreeCube)

theorem sphereCandidate_generates_iff_hopfEndpoint :
    Function.Surjective (fun k : ℤ ↦ ComplexCrossProductUnitary.sphereCandidateClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ hopfEndpointClass A hA ^ k) := by
  rw [sphereCandidate_generates_iff_hopfLatitude]
  have h := CyclicGenerators.equiv_generates_iff (hopfFrameConnectingMulEquiv A hA)
    hopfLatitudeInputClass
  rw [hopfFrameConnectingMulEquiv_latitude] at h
  exact h.symm

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
