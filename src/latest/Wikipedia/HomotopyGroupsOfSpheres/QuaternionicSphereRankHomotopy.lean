import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicRankReductionHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.LatitudeHomotopyDescent
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSphereCandidateClass

/-! # Rank reduction compared on the actual seven-sphere, fixing its base point -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix QuaternionicColumns
open Wikipedia.HopfProblem.SphereHomology

attribute [local irreducible] rankReductionHomotopy
attribute [local irreducible] twoCubeFamily reducedCubeFamily symmetricMap sphereFiveHomeomorph

def swapConjugation : SpGroup (Fin 3) ≃ₜ SpGroup (Fin 3) :=
  (Homeomorph.mulLeft swap).trans (Homeomorph.mulRight swap⁻¹)

theorem swapConjugation_apply (A : SpGroup (Fin 3)) :
    swapConjugation A = swap * A * swap⁻¹ := rfl

theorem swapConjugation_one : swapConjugation 1 = 1 := by
  rw [swapConjugation_apply, mul_one, mul_inv_cancel]

def unreducedSphereFamily : LatitudeDescent.DoubleFamily 5 (SpGroup (Fin 3)) 1 where
  map := twoCubeFamily.comp
    ⟨fun p ↦ (symmetricMap (sphereFiveHomeomorph p.2.2), ![p.1, p.2.1]), by fun_prop⟩
  outer_zero t z := twoCubeFamily_boundary _ _ ⟨0, Or.inl rfl⟩
  outer_one t z := twoCubeFamily_boundary _ _ ⟨0, Or.inr rfl⟩
  inner_zero s z := twoCubeFamily_boundary _ _ ⟨1, Or.inl rfl⟩
  inner_one s z := twoCubeFamily_boundary _ _ ⟨1, Or.inr rfl⟩

def unreducedSphereCandidate : C(Sphere 7, SpGroup (Fin 3)) :=
  unreducedSphereFamily.toSphereMap

theorem unreducedSphereCandidate_sourcePoint (s t : I) (z : UnitSphere) :
    unreducedSphereCandidate (sphereSourcePoint s t z) = twoCubeMap (symmetricMap z) ![s, t] := by
  change unreducedSphereFamily.toSphereMap
    (Latitude.point 6 s (Latitude.point 5 t (sphereFiveHomeomorph.symm z))) = _
  rw [LatitudeDescent.DoubleFamily.toSphereMap_point]
  change twoCubeFamily (symmetricMap (sphereFiveHomeomorph (sphereFiveHomeomorph.symm z)),
    ![s, t]) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

def conjugatedSphereFamily : LatitudeDescent.DoubleFamily 5 (SpGroup (Fin 3)) 1 where
  map := (swapConjugation : C(_, _)).comp unreducedSphereFamily.map
  outer_zero t z := by
    change swapConjugation (unreducedSphereFamily.map (0, (t, z))) = 1
    rw [unreducedSphereFamily.outer_zero, swapConjugation_one]
  outer_one t z := by
    change swapConjugation (unreducedSphereFamily.map (1, (t, z))) = 1
    rw [unreducedSphereFamily.outer_one, swapConjugation_one]
  inner_zero s z := by
    change swapConjugation (unreducedSphereFamily.map (s, (0, z))) = 1
    rw [unreducedSphereFamily.inner_zero, swapConjugation_one]
  inner_one s z := by
    change swapConjugation (unreducedSphereFamily.map (s, (1, z))) = 1
    rw [unreducedSphereFamily.inner_one, swapConjugation_one]

def stabilizationContinuousMap : C(SpGroup (Fin 2), SpGroup (Fin 3)) :=
  ⟨stabilization 2, continuous_stabilization 2⟩

def stabilizedSphereFamily : LatitudeDescent.DoubleFamily 5 (SpGroup (Fin 3)) 1 where
  map := stabilizationContinuousMap.comp sphereCandidateFamily.map
  outer_zero t z := by
    change stabilization 2 (sphereCandidateFamily.map (0, (t, z))) = 1
    rw [sphereCandidateFamily.outer_zero, map_one]
  outer_one t z := by
    change stabilization 2 (sphereCandidateFamily.map (1, (t, z))) = 1
    rw [sphereCandidateFamily.outer_one, map_one]
  inner_zero s z := by
    change stabilization 2 (sphereCandidateFamily.map (s, (0, z))) = 1
    rw [sphereCandidateFamily.inner_zero, map_one]
  inner_one s z := by
    change stabilization 2 (sphereCandidateFamily.map (s, (1, z))) = 1
    rw [sphereCandidateFamily.inner_one, map_one]

def latitudeCubeParameter : C(I × (I × Sphere 5),
    QuaternionicSymmetricMatrices.Space (Fin 3) × (Fin 2 → I)) :=
  ⟨fun p ↦ (symmetricMap (sphereFiveHomeomorph p.2.2), ![p.1, p.2.1]), by fun_prop⟩

def latitudeRankHomotopy : conjugatedSphereFamily.map.Homotopy stabilizedSphereFamily.map := by
  let H := rankReductionHomotopy.compContinuousMap latitudeCubeParameter
  have h0 : conjugatedTwoCubeFamily.comp latitudeCubeParameter = conjugatedSphereFamily.map := by
    apply ContinuousMap.ext
    intro p
    rfl
  have h1 : stabilizedReducedTwoCubeFamily.comp latitudeCubeParameter =
      stabilizedSphereFamily.map := by
    apply ContinuousMap.ext
    intro p
    rfl
  exact H.cast h0 h1

theorem latitudeRankHomotopy_boundary (r s t : I) (z : Sphere 5)
    (h : s = 0 ∨ s = 1 ∨ t = 0 ∨ t = 1) :
    latitudeRankHomotopy (r, (s, (t, z))) = 1 := by
  apply rankReductionHomotopy_boundary
  rcases h with h | h | h | h
  · exact ⟨0, Or.inl h⟩
  · exact ⟨0, Or.inr h⟩
  · exact ⟨1, Or.inl h⟩
  · exact ⟨1, Or.inr h⟩

def sphereRankHomotopyAux :
    conjugatedSphereFamily.toSphereMap.Homotopy stabilizedSphereFamily.toSphereMap :=
  LatitudeDescent.DoubleFamily.homotopyDescent _ _ latitudeRankHomotopy
    (fun r t z ↦ latitudeRankHomotopy_boundary r 0 t z (Or.inl rfl))
    (fun r t z ↦ latitudeRankHomotopy_boundary r 1 t z (Or.inr (Or.inl rfl)))
    (fun r s z ↦ latitudeRankHomotopy_boundary r s 0 z (Or.inr (Or.inr (Or.inl rfl))))
    (fun r s z ↦ latitudeRankHomotopy_boundary r s 1 z (Or.inr (Or.inr (Or.inr rfl))))

theorem conjugatedSphereFamily_toSphereMap :
    conjugatedSphereFamily.toSphereMap =
      (swapConjugation : C(_, _)).comp unreducedSphereCandidate := by
  apply ContinuousMap.ext
  intro w
  obtain ⟨⟨s, v⟩, rfl⟩ := Latitude.point_surjective 6 w
  obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective 5 v
  change conjugatedSphereFamily.toSphereMap (Latitude.point 6 s (Latitude.point 5 t z)) =
    swapConjugation (unreducedSphereFamily.toSphereMap
      (Latitude.point 6 s (Latitude.point 5 t z)))
  rw [LatitudeDescent.DoubleFamily.toSphereMap_point,
    LatitudeDescent.DoubleFamily.toSphereMap_point]
  rfl

theorem stabilizedSphereFamily_toSphereMap :
    stabilizedSphereFamily.toSphereMap = stabilizationContinuousMap.comp sphereCandidate := by
  apply ContinuousMap.ext
  intro w
  obtain ⟨⟨s, v⟩, rfl⟩ := Latitude.point_surjective 6 w
  obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective 5 v
  change stabilizedSphereFamily.toSphereMap (Latitude.point 6 s (Latitude.point 5 t z)) =
    stabilizationContinuousMap (sphereCandidateFamily.toSphereMap
      (Latitude.point 6 s (Latitude.point 5 t z)))
  rw [LatitudeDescent.DoubleFamily.toSphereMap_point,
    LatitudeDescent.DoubleFamily.toSphereMap_point]
  rfl

def sphereRankHomotopy :
    ((swapConjugation : C(_, _)).comp unreducedSphereCandidate).Homotopy
      (stabilizationContinuousMap.comp sphereCandidate) :=
  sphereRankHomotopyAux.cast conjugatedSphereFamily_toSphereMap stabilizedSphereFamily_toSphereMap

theorem sphereRankHomotopy_sourcePoint (r s t : I) (z : UnitSphere) :
    sphereRankHomotopy (r, sphereSourcePoint s t z) =
      rankReductionHomotopy (r, (symmetricMap z, ![s, t])) := by
  change sphereRankHomotopyAux (r, Latitude.point 6 s
    (Latitude.point 5 t (sphereFiveHomeomorph.symm z))) = _
  rw [sphereRankHomotopyAux, LatitudeDescent.DoubleFamily.homotopyDescent_point]
  change rankReductionHomotopy
    (r, (symmetricMap (sphereFiveHomeomorph (sphereFiveHomeomorph.symm z)), ![s, t])) = _
  rw [Homeomorph.apply_symm_apply]

theorem sphereRankHomotopy_basepoint (r : I) :
    sphereRankHomotopy (r, sphereCandidateBasepoint) = 1 := by
  rw [sphereCandidateBasepoint, sphereRankHomotopy_sourcePoint]
  exact rankReductionHomotopy_boundary r _ _ ⟨0, Or.inl rfl⟩

def sphereRankHomotopyRel :
    ((swapConjugation : C(_, _)).comp unreducedSphereCandidate).HomotopyRel
      (stabilizationContinuousMap.comp sphereCandidate) {sphereCandidateBasepoint} where
  toHomotopy := sphereRankHomotopy
  prop' r w hw := by
    have he : w = sphereCandidateBasepoint := hw
    subst w
    change sphereRankHomotopy (r, sphereCandidateBasepoint) = _
    rw [sphereRankHomotopy_basepoint]
    exact ((sphereRankHomotopy.apply_zero sphereCandidateBasepoint).symm.trans
      (sphereRankHomotopy_basepoint 0)).symm

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
