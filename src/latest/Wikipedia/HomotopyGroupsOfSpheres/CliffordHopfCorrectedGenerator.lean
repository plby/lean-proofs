import Wikipedia.HomotopyGroupsOfSpheres.CliffordHopfCorrection
import Wikipedia.HomotopyGroupsOfSpheres.CliffordRawGenerator

/-! # The raw candidate class is unchanged by the actual based Hopf correction -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

def hopfCorrectedInputClass : π_ 4 (BalancedRealInvolutions.Space 6) (rawBalanced pole) :=
  ⟦hopfCorrectedCube parameterFourCube⟧

theorem rawInputClass_eq_hopfCorrectedInputClass : rawInputClass = hopfCorrectedInputClass :=
  rawClass_eq_hopfCorrected parameterFourCube

theorem sphereCandidate_generates_iff_hopfCorrected :
    Function.Surjective (fun k : ℤ ↦ ComplexCrossProductUnitary.sphereCandidateClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ hopfCorrectedInputClass ^ k) := by
  rw [sphereCandidate_generates_iff_raw, rawInputClass_eq_hopfCorrectedInputClass]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
