import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSphereCandidate
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicTwelvePreimages

/-!
# Exactly twelve preimages for the actual seven-sphere map

The global latitude parametrization is surjective. The earlier exclusion
theorem forces every selected-target preimage onto both equators, where
the parametrization is injective in the original five-sphere variable.
Thus the count is now a statement about points of the actual seven-sphere.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix
open Wikipedia.HopfProblem.SphereHomology

def parameterMidpoint : I := ⟨1 / 2, by constructor <;> norm_num⟩

theorem parameterMidpoint_ne_zero : parameterMidpoint ≠ 0 := by
  intro h
  have he := congrArg (fun t : I ↦ (t : ℝ)) h
  norm_num [parameterMidpoint] at he

theorem parameterMidpoint_ne_one : parameterMidpoint ≠ 1 := by
  intro h
  have he := congrArg (fun t : I ↦ (t : ℝ)) h
  norm_num [parameterMidpoint] at he

theorem parameterMidpoint_angle : (parameterMidpoint : ℝ) * Real.pi = Real.pi / 2 := by
  change (1 / 2 : ℝ) * Real.pi = Real.pi / 2
  ring

theorem unitParameter_angle_bounds (s : I) : (s : ℝ) * Real.pi ∈ Set.Icc 0 Real.pi := by
  refine ⟨mul_nonneg s.property.1 Real.pi_pos.le, ?_⟩
  simpa only [one_mul] using mul_le_mul_of_nonneg_right s.property.2 Real.pi_pos.le

theorem unitParameter_eq_midpoint (s : I) (h : (s : ℝ) * Real.pi = Real.pi / 2) :
    s = parameterMidpoint := by
  apply Subtype.ext
  apply mul_right_cancel₀ Real.pi_ne_zero
  exact h.trans parameterMidpoint_angle.symm

theorem midpointLatitude_injective (n : ℕ) :
    Function.Injective (Latitude.point n parameterMidpoint) := by
  intro z w h
  rcases ((Latitude.point_eq_iff n parameterMidpoint parameterMidpoint z w).mp h).2 with h | h | h
  · exact (parameterMidpoint_ne_zero h).elim
  · exact (parameterMidpoint_ne_one h).elim
  · exact h

def midpointSphereEmbedding : UnitSphere ↪ Sphere 7 where
  toFun := sphereSourcePoint parameterMidpoint parameterMidpoint
  inj' := by
    intro z w h
    apply sphereFiveHomeomorph.symm.injective
    apply midpointLatitude_injective 5
    apply midpointLatitude_injective 6
    exact h

def sphereCandidateTargetPreimage : Set (Sphere 7) :=
  {x | (sphereCandidateProjection x).val = targetColumn}

theorem sphereCandidateTargetPreimage_eq_image :
    sphereCandidateTargetPreimage = midpointSphereEmbedding '' midpointTargetPreimage := by
  ext w
  constructor
  · intro h
    obtain ⟨⟨s, t, z⟩, rfl⟩ := sphereSourcePoint_surjective w
    change (sphereCandidateProjection (sphereSourcePoint s t z)).val = targetColumn at h
    rw [sphereCandidateProjection_sourcePoint] at h
    obtain ⟨hs, ht⟩ := target_parameter_midpoint _ _ (symmetricMap z)
      (unitParameter_angle_bounds s) (unitParameter_angle_bounds t) h
    refine ⟨z, ?_, ?_⟩
    · change firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn
      simpa only [hs, ht] using h
    · change sphereSourcePoint parameterMidpoint parameterMidpoint z = sphereSourcePoint s t z
      rw [unitParameter_eq_midpoint s hs, unitParameter_eq_midpoint t ht]
  · rintro ⟨z, hz, rfl⟩
    change (sphereCandidateProjection
      (sphereSourcePoint parameterMidpoint parameterMidpoint z)).val = targetColumn
    rw [sphereCandidateProjection_sourcePoint, parameterMidpoint_angle]
    exact hz

theorem sphereCandidateTargetPreimage_finite : sphereCandidateTargetPreimage.Finite := by
  rw [sphereCandidateTargetPreimage_eq_image]
  exact midpointTargetPreimage_finite.image midpointSphereEmbedding

theorem sphereCandidateTargetPreimage_ncard_eq_twelve :
    sphereCandidateTargetPreimage.ncard = 12 := by
  rw [sphereCandidateTargetPreimage_eq_image,
    Set.ncard_image_of_injective _ midpointSphereEmbedding.injective,
    midpointTargetPreimage_ncard_eq_twelve]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
