import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMatrixLatitudeFamily

/-! # The parameter homeomorphism preserves surjectivity of the actual native map -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicColumns LatitudeDescent.DoubleFamily

def matrixLatitudeClass : π_ 7 (SpGroup (Fin 12)) 1 :=
  pointedMap (N := Fin 7) stableMatrixFamily.toSphereMap (latitudeBasepoint 5) 1
    stableMatrixFamily.toSphereMap_latitudeBasepoint (sphereSevenGenerator (latitudeBasepoint 5))

theorem stableSphereCandidateClass_generates_iff_surjective (r : ℕ) :
    Function.Surjective (fun k : ℤ ↦ stableSphereCandidateClass r ^ k) ↔
      Function.Surjective (pointedMap (N := Fin 7) (stableSphereCandidate r)
        sphereCandidateBasepoint 1 (stableSphereCandidate_basepoint r)) :=
  sphereSevenMap_generates_iff_surjective (stableSphereCandidate r)
    sphereCandidateBasepoint 1 (stableSphereCandidate_basepoint r)

theorem matrixLatitudeClass_generates_iff_surjective :
    Function.Surjective (fun k : ℤ ↦ matrixLatitudeClass ^ k) ↔
      Function.Surjective (pointedMap (N := Fin 7) stableMatrixFamily.toSphereMap
        (latitudeBasepoint 5) 1 stableMatrixFamily.toSphereMap_latitudeBasepoint) :=
  sphereSevenMap_generates_iff_surjective stableMatrixFamily.toSphereMap
    (latitudeBasepoint 5) 1 stableMatrixFamily.toSphereMap_latitudeBasepoint

theorem matrixCandidate_map_surjective_iff_latitude :
    Function.Surjective (pointedMap (N := Fin 7) (stableSphereCandidate 9)
      sphereCandidateBasepoint 1 (stableSphereCandidate_basepoint 9)) ↔
    Function.Surjective (pointedMap (N := Fin 7) stableMatrixFamily.toSphereMap
      (latitudeBasepoint 5) 1 stableMatrixFamily.toSphereMap_latitudeBasepoint) :=
  (pointedMap_surjective_precompose_homeomorph_iff (N := Fin 7)
    parameterSourceHomeomorph (stableSphereCandidate 9) stableMatrixFamily.toSphereMap
    (latitudeBasepoint 5) sphereCandidateBasepoint 1 parameterSourceHomeomorph_basepoint
    (stableSphereCandidate_basepoint 9) stableMatrixFamily.toSphereMap_latitudeBasepoint
    stableMatrixFamily_toSphereMap.symm).symm

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
