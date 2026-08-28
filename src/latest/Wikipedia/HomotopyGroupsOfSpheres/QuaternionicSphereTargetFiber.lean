import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSphereCandidateClass
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicGeneratorDegree

/-! # The exact native degree map has the counted twelve-point fiber -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicFibration QuaternionicColumns QuaternionicBottMatrix

theorem projection_eq_iff_column_eq (A B : SpTwo) :
    projection A = projection B ↔ column 0 A = column 0 B := by
  constructor
  · intro h
    have hp := congrArg (fun x : BaseSphere ↦ x.val.ofLp) h
    apply Subtype.ext
    funext r
    fin_cases r
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp
  · intro h
    apply Subtype.ext
    change WithLp.toLp 2 (A.val 0 0, A.val 1 0) = WithLp.toLp 2 (B.val 0 0, B.val 1 0)
    apply congrArg (WithLp.toLp 2)
    exact Prod.ext (congrArg (fun x : UnitColumn (Fin 2) ↦ x.val 0) h)
      (congrArg (fun x : UnitColumn (Fin 2) ↦ x.val 1) h)

theorem sphereCandidateDegreeMap_eq_iff (x y : Sphere 7) :
    sphereCandidateDegreeMap x = sphereCandidateDegreeMap y ↔
      sphereCandidateProjection x = sphereCandidateProjection y := by
  change baseSphereHomeomorph (projection (sphereCandidate x)) =
    baseSphereHomeomorph (projection (sphereCandidate y)) ↔ _
  rw [baseSphereHomeomorph.injective.eq_iff]
  exact projection_eq_iff_column_eq (sphereCandidate x) (sphereCandidate y)

theorem sphereCandidateProjection_seed :
    (sphereCandidateProjection (midpointSphereEmbedding MidpointSeed.input)).val =
      targetColumn := by
  change (sphereCandidateProjection
    (sphereSourcePoint parameterMidpoint parameterMidpoint MidpointSeed.input)).val = _
  rw [sphereCandidateProjection_sourcePoint, parameterMidpoint_angle]
  exact MidpointSeed.input_hits_target

def sphereCandidateTarget : Sphere 7 :=
  sphereCandidateDegreeMap (midpointSphereEmbedding MidpointSeed.input)

theorem sphereCandidateDegreeMap_fiber :
    {x | sphereCandidateDegreeMap x = sphereCandidateTarget} = sphereCandidateTargetPreimage := by
  ext x
  change sphereCandidateDegreeMap x =
    sphereCandidateDegreeMap (midpointSphereEmbedding MidpointSeed.input) ↔
      (sphereCandidateProjection x).val = targetColumn
  rw [sphereCandidateDegreeMap_eq_iff]
  constructor
  · intro h
    exact (congrArg Subtype.val h).trans sphereCandidateProjection_seed
  · intro h
    exact Subtype.ext (h.trans sphereCandidateProjection_seed.symm)

/-- The fiber count concerns the literal self-map whose degree occurs in the exact sequence. -/
theorem sphereCandidateDegreeMap_fiber_ncard :
    {x | sphereCandidateDegreeMap x = sphereCandidateTarget}.ncard = 12 := by
  rw [sphereCandidateDegreeMap_fiber, sphereCandidateTargetPreimage_ncard_eq_twelve]

/-- The remaining generator issue is retained explicitly in the degree formula. -/
theorem sphereCandidateDegree_eq_coordinate_mul_generator :
    sphereSevenDegree sphereCandidateDegreeMap =
      (piSevenSpTwoMulEquiv sphereCandidateClass).toAdd * generatorProjectionDegree := by
  rw [← sphereCandidateClass_projectionDegree]
  exact projectionDegree_toAdd sphereCandidateClass

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
