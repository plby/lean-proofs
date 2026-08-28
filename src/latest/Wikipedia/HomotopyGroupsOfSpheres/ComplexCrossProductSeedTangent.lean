import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductSphereDifferential

/-!
# An unconditional tangent equivalence at the explicit diagonal seed

The diagonal square roots are built from the nonzero sphere coordinates,
not assumed. The previous radial-kernel calculation proves injectivity of
the actual sphere differential; the two five-dimensional spaces then agree.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix QuaternionicSymmetricMatrices RealSymmetricMixing

def coordinateUnitPhase (c : ℂ) (hc : c ≠ 0) : unitary ℂ :=
  ⟨c / star c, Unitary.mem_iff_self_mul_star.mpr (by
    rw [star_div₀, star_star]
    field_simp [hc, star_ne_zero.mpr hc])⟩

theorem coordinateUnitPhase_sq (c d : ℂ) (hc : c ≠ 0) (hd : c ^ 2 = d * star c ^ 2) :
    (coordinateUnitPhase c hc).val ^ 2 = d := by
  change (c / star c) ^ 2 = d
  rw [div_pow]
  exact (div_eq_iff (pow_ne_zero 2 (star_ne_zero.mpr hc))).mpr hd

theorem sphereSymmetricDifferential_diagonal_kernel (z : UnitSphere)
    (d : Fin 3 → ℂ) (hd : (symmetricMap z).val.val = Matrix.diagonal d)
    (hcoord : ∀ r, z.val r ≠ 0) (htrace : Complex.normSq (squareSum z.val) < 1)
    (hdet : (radialMatrix z.val).det ≠ 0) (v : SphereCenteredCoordinates.Tangent z)
    (hv : sphereSymmetricDifferential z v = 0) : v = 0 := by
  have hv' : symmetricVariation z.val v.val = 0 := by
    simpa only [sphereSymmetricDifferential_apply] using hv
  have he := sphere_curve_diagonal_kernel
    (fun t : ℝ ↦ SphereCenteredCoordinates.inverse z (t • v)) v.val 0
    (hasDerivAt_sphereInverse_line_entry z v)
    (by simpa only [zero_smul, SphereCenteredCoordinates.inverse_zero] using hv') d
    (by simpa only [zero_smul, SphereCenteredCoordinates.inverse_zero] using hd)
    (by simpa only [zero_smul, SphereCenteredCoordinates.inverse_zero] using hcoord)
    (by simpa only [zero_smul, SphereCenteredCoordinates.inverse_zero] using htrace)
    (by simpa only [zero_smul, SphereCenteredCoordinates.inverse_zero] using hdet)
  apply Subtype.ext
  exact congrArg (WithLp.toLp 2) he

theorem sphereSymmetricDifferential_diagonal_injective (z : UnitSphere)
    (d : Fin 3 → ℂ) (hd : (symmetricMap z).val.val = Matrix.diagonal d)
    (hcoord : ∀ r, z.val r ≠ 0) (htrace : Complex.normSq (squareSum z.val) < 1)
    (hdet : (radialMatrix z.val).det ≠ 0) : Function.Injective (sphereSymmetricDifferential z) := by
  intro v w h
  have he : sphereSymmetricDifferential z (v - w) = 0 := by rw [map_sub, h, sub_self]
  exact sub_eq_zero.mp
    (sphereSymmetricDifferential_diagonal_kernel z d hd hcoord htrace hdet (v - w) he)

namespace MidpointSeed

def diagonalPhases (r : Fin 3) : unitary ℂ :=
  coordinateUnitPhase (rotatedInput.val r) (rotatedInput_coordinate_ne_zero r)

theorem diagonalPhases_sq (r : Fin 3) : (diagonalPhases r).val ^ 2 = -targetEigenvalues r :=
  coordinateUnitPhase_sq _ _ (rotatedInput_coordinate_ne_zero r)
    (diagonal_phase_equation rotatedInput _ symmetricMap_rotatedInput r)

theorem symmetricMap_rotatedInput_phase_square : (symmetricMap rotatedInput).val.val =
    Matrix.diagonal (fun r ↦ (diagonalPhases r).val ^ 2) := by
  rw [symmetricMap_rotatedInput]
  simp only [diagonalPhases_sq]

theorem rotatedInput_squareSum_normSq_lt_one : Complex.normSq (squareSum rotatedInput.val) < 1 := by
  have he := midpoint_squareSum_normSq_lt_one input input_hits_target
  change Complex.normSq (squareSum (targetRotation *ᵥ rotatedInput.val)) < 1 at he
  simpa only [squareSum_targetRotation] using he

theorem sphereSymmetricDifferential_injective :
    Function.Injective (sphereSymmetricDifferential rotatedInput) :=
  sphereSymmetricDifferential_diagonal_injective rotatedInput _ symmetricMap_rotatedInput
    rotatedInput_coordinate_ne_zero rotatedInput_squareSum_normSq_lt_one
    (ne_of_gt radialMatrix_rotatedInput_det_pos)

def tangentModelEquiv :
    SphereCenteredCoordinates.Tangent rotatedInput ≃ₗ[ℝ] DirectionSpace (Fin 3) :=
  sphereDiagonalDifferentialEquiv rotatedInput diagonalPhases
    symmetricMap_rotatedInput_phase_square sphereSymmetricDifferential_injective

theorem tangentModelEquiv_apply (v : SphereCenteredCoordinates.Tangent rotatedInput) :
    tangentModelEquiv v = sphereDiagonalDifferential rotatedInput diagonalPhases
      symmetricMap_rotatedInput_phase_square v := rfl

end MidpointSeed
end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
