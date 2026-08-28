import Wikipedia.HomotopyGroupsOfSpheres.LatitudeDescent
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicReducedFirstColumn
import Wikipedia.HomotopyGroupsOfSpheres.SphereCoordinateIsometries

/-!
# The explicit candidate is a map from the actual seven-sphere to Sp(2)

The two angular boundary faces collapse exactly as required for successive
latitude quotients. The resulting continuous sphere map retains the original
reduced matrix family and its exact first-column formula.
-/

noncomputable section

open scoped unitInterval Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix QuaternionicColumns
open Wikipedia.HopfProblem.SphereHomology

local notation "Ambient" => EuclideanSpace ℂ (Fin 3)

theorem complexAmbient_finrank : Module.finrank ℝ Ambient = 6 := by
  rw [(WithLp.linearEquiv 2 ℝ (Fin 3 → ℂ)).finrank_eq, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex]

def complexRealCoordinates : Ambient ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 6) :=
  ((stdOrthonormalBasis ℝ Ambient).reindex (finCongr complexAmbient_finrank)).repr

def sphereFiveHomeomorph : Sphere 5 ≃ₜ UnitSphere :=
  (SphereCenteredCoordinates.sphereIsometry complexRealCoordinates).symm

def sphereCandidateFamily : LatitudeDescent.DoubleFamily 5 (SpGroup (Fin 2)) 1 where
  map := reducedCubeFamily.comp
    ⟨fun p ↦ (symmetricMap (sphereFiveHomeomorph p.2.2), ![p.1, p.2.1]), by fun_prop⟩
  outer_zero t z := reducedCubeFamily_boundary _ _ ⟨0, Or.inl rfl⟩
  outer_one t z := reducedCubeFamily_boundary _ _ ⟨0, Or.inr rfl⟩
  inner_zero s z := reducedCubeFamily_boundary _ _ ⟨1, Or.inl rfl⟩
  inner_one s z := reducedCubeFamily_boundary _ _ ⟨1, Or.inr rfl⟩

def sphereCandidate : C(Sphere 7, SpGroup (Fin 2)) := sphereCandidateFamily.toSphereMap

def sphereSourcePoint (s t : I) (z : UnitSphere) : Sphere 7 :=
  Latitude.point 6 s (Latitude.point 5 t (sphereFiveHomeomorph.symm z))

theorem continuous_sphereSourcePoint :
    Continuous (fun p : I × (I × UnitSphere) ↦ sphereSourcePoint p.1 p.2.1 p.2.2) := by
  unfold sphereSourcePoint
  fun_prop

theorem sphereSourcePoint_surjective :
    Function.Surjective (fun p : I × (I × UnitSphere) ↦ sphereSourcePoint p.1 p.2.1 p.2.2) := by
  intro w
  obtain ⟨⟨s, v⟩, rfl⟩ := Latitude.point_surjective 6 w
  obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective 5 v
  refine ⟨(s, (t, sphereFiveHomeomorph z)), ?_⟩
  change Latitude.point 6 s
    (Latitude.point 5 t (sphereFiveHomeomorph.symm (sphereFiveHomeomorph z))) = _
  rw [Homeomorph.symm_apply_apply]

theorem sphereCandidate_sourcePoint (s t : I) (z : UnitSphere) :
    sphereCandidate (sphereSourcePoint s t z) = reducedTwoCubeMap (symmetricMap z) ![s, t] := by
  change sphereCandidateFamily.toSphereMap
    (Latitude.point 6 s (Latitude.point 5 t (sphereFiveHomeomorph.symm z))) = _
  rw [LatitudeDescent.DoubleFamily.toSphereMap_point]
  change reducedCubeFamily (symmetricMap (sphereFiveHomeomorph (sphereFiveHomeomorph.symm z)),
    ![s, t]) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem sphereCandidate_outer_zero (v : Sphere 6) :
    sphereCandidate (Latitude.point 6 0 v) = 1 := by
  obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective 5 v
  rw [sphereCandidate, LatitudeDescent.DoubleFamily.toSphereMap_point]
  exact sphereCandidateFamily.outer_zero t z

theorem sphereCandidate_outer_one (v : Sphere 6) :
    sphereCandidate (Latitude.point 6 1 v) = 1 := by
  obtain ⟨⟨t, z⟩, rfl⟩ := Latitude.point_surjective 5 v
  rw [sphereCandidate, LatitudeDescent.DoubleFamily.toSphereMap_point]
  exact sphereCandidateFamily.outer_one t z

def sphereCandidateProjection : C(Sphere 7, UnitColumn (Fin 2)) := (column 0).comp sphereCandidate

theorem sphereCandidateProjection_sourcePoint (s t : I) (z : UnitSphere) :
    (sphereCandidateProjection (sphereSourcePoint s t z)).val =
      firstColumnFormula ((s : ℝ) * Real.pi) ((t : ℝ) * Real.pi) (symmetricMap z) := by
  change (column 0 (sphereCandidate (sphereSourcePoint s t z))).val = _
  rw [sphereCandidate_sourcePoint]
  funext r
  exact reducedTwoCubeMap_first_column (symmetricMap z) ![s, t] r

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
