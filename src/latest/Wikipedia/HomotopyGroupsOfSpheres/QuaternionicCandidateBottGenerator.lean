import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCandidateClassComparison

/-!
# The degree-twelve candidate generates exactly when the stable Bott input does

All changes of matrix rank, parameter base point, sphere/cube quotient, and
operator model are the actual proved maps. Only primitivity of the explicit
stable five-sphere input remains in this generator comparison.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicColumns LatitudeDescent.DoubleFamily

attribute [local irreducible] pointedMap sphereSevenGenerator matrixBottInputMulEquiv
  stableInputClass stableCandidateRankMulEquiv sphereCandidateClass

theorem matrixCandidate_generates_iff_latitude :
    Function.Surjective (fun k : ℤ ↦ stableSphereCandidateClass 9 ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ matrixLatitudeClass ^ k) :=
  (stableSphereCandidateClass_generates_iff_surjective 9).trans
    (matrixCandidate_map_surjective_iff_latitude.trans
      matrixLatitudeClass_generates_iff_surjective.symm)

theorem matrixLatitude_generates_iff_input :
    Function.Surjective (fun k : ℤ ↦ matrixLatitudeClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ stableInputClass 9 ^ k) := by
  have h := stableMatrixFamily.nativeCube_generates_iff stableMatrixFamily_parameter_point
  change Function.Surjective (fun k : ℤ ↦ matrixLatitudeClass ^ k) ↔
    Function.Surjective (fun k : ℤ ↦
      stableMatrixFamily.nativeClass stableMatrixFamily_parameter_point ^ k) at h
  rw [stableMatrixFamily_nativeClass] at h
  exact h.trans (nativeEquiv_generates_iff (N := Fin 5) (M := Fin 7)
    matrixBottInputMulEquiv (stableInputClass 9))

theorem sphereCandidate_generates_iff_stableInput :
    Function.Surjective (fun k : ℤ ↦ sphereCandidateClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ stableInputClass 9 ^ k) := by
  have h := nativeEquiv_generates_iff (N := Fin 7) (M := Fin 7)
    (stableCandidateRankMulEquiv 9) sphereCandidateClass
  rw [stableCandidateRankMulEquiv_candidate] at h
  exact h.symm.trans (matrixCandidate_generates_iff_latitude.trans
    matrixLatitude_generates_iff_input)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
