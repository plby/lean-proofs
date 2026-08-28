import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordStableInput
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCandidateBottGenerator

/-! # Generation by the degree-twelve sphere candidate reduces to the explicit Clifford class -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open ComplexCrossProductUnitary

attribute [local irreducible] stableCliffordClass stableInputClass

theorem stableInput_generates_iff_clifford :
    Function.Surjective (fun k : ℤ ↦ stableInputClass 9 ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ stableCliffordClass ^ k) := by
  rw [stableCliffordClass_eq_stableInput]

theorem sphereCandidate_generates_iff_clifford :
    Function.Surjective (fun k : ℤ ↦ sphereCandidateClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ stableCliffordClass ^ k) :=
  sphereCandidate_generates_iff_stableInput.trans stableInput_generates_iff_clifford

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
