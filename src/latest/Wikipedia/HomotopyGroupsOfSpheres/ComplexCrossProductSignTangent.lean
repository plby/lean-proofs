import Wikipedia.HomotopyGroupsOfSpheres.ComplexSphereSignCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricTraceZeroSignOrientation

/-!
# The sign action on the polynomial map's actual tangent differential

Diagonal normalization intertwines the actual derivative with the checked
sign conjugation on the real symmetric trace-zero model. At the explicit
seed this gives a determinant-one source tangent automorphism and an exact
comparison of the matrix derivatives at all four sign-related inputs.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicSymmetricMatrices RealSymmetricMixing

theorem realSigns_coe_complex (x y : Bool) (r : Fin 3) : (realSigns x y r : ℂ) = signs x y r := by
  apply Complex.ext
  · rfl
  · have he := congrArg Complex.im (signs_star x y r)
    simp only [Complex.star_def, Complex.conj_im] at he
    change (0 : ℝ) = (signs x y r).im
    linarith

theorem diagonalTangentCoordinates_sign (q : Fin 3 → unitary ℂ) (x y : Bool)
    (D : Matrix (Fin 3) (Fin 3) ℂ) :
    diagonalTangentCoordinates q (signMatrix x y * D * signMatrix x y) =
      Matrix.diagonal (realSigns x y) * diagonalTangentCoordinates q D *
        Matrix.diagonal (realSigns x y) := by
  ext r s
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  change (star (q r).val * ((signMatrix x y * D * signMatrix x y) r s) * star (q s).val).im =
    realSigns x y r * (star (q r).val * D r s * star (q s).val).im * realSigns x y s
  simp only [signMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have he : star (q r).val * (signs x y r * D r s * signs x y s) * star (q s).val =
      (realSigns x y r : ℂ) * (star (q r).val * D r s * star (q s).val) *
        (realSigns x y s : ℂ) := by
    rw [realSigns_coe_complex, realSigns_coe_complex]
    ring
  rw [he]
  simp [Complex.mul_im]

theorem sphereDiagonalDifferential_sign (z : UnitSphere) (q : Fin 3 → unitary ℂ)
    (hq : (symmetricMap z).val.val = Matrix.diagonal (fun r ↦ (q r).val ^ 2))
    (x y : Bool)
    (hqs : (symmetricMap (signSphere x y z)).val.val =
      Matrix.diagonal (fun r ↦ (q r).val ^ 2))
    (v : SphereCenteredCoordinates.Tangent z) :
    sphereDiagonalDifferential (signSphere x y z) q hqs (signTangentEquiv x y z v) =
      threeSignDirection x y (sphereDiagonalDifferential z q hq v) := by
  apply Subtype.ext
  rw [threeSignDirection_val]
  change diagonalTangentCoordinates q
    (sphereSymmetricDifferential (signSphere x y z) (signTangentEquiv x y z v)) =
      Matrix.diagonal (realSigns x y) *
        diagonalTangentCoordinates q (sphereSymmetricDifferential z v) *
          Matrix.diagonal (realSigns x y)
  rw [sphereSymmetricDifferential_sign, diagonalTangentCoordinates_sign]

namespace MidpointSeed

def signTangentComparison (x y : Bool) :
    SphereCenteredCoordinates.Tangent rotatedInput →ₗ[ℝ]
      SphereCenteredCoordinates.Tangent rotatedInput :=
  tangentModelEquiv.symm.toLinearMap.comp
    ((threeSignDirection x y).comp tangentModelEquiv.toLinearMap)

theorem signTangentComparison_det (x y : Bool) : (signTangentComparison x y).det = 1 := by
  calc
    _ = (threeSignDirection x y).det := LinearMap.det_conj _ tangentModelEquiv.symm
    _ = 1 := threeSignDirection_det x y

theorem signInput_diagonal_phase_square (x y : Bool) :
    (symmetricMap (signSphere x y rotatedInput)).val.val =
      Matrix.diagonal (fun r ↦ (diagonalPhases r).val ^ 2) :=
  diagonal_signSphere x y rotatedInput _ symmetricMap_rotatedInput_phase_square

theorem sign_tangent_model_comparison (x y : Bool)
    (v : SphereCenteredCoordinates.Tangent rotatedInput) :
    sphereDiagonalDifferential (signSphere x y rotatedInput) diagonalPhases
        (signInput_diagonal_phase_square x y) (signTangentEquiv x y rotatedInput v) =
      sphereDiagonalDifferential rotatedInput diagonalPhases symmetricMap_rotatedInput_phase_square
        (signTangentComparison x y v) := by
  rw [sphereDiagonalDifferential_sign rotatedInput diagonalPhases
    symmetricMap_rotatedInput_phase_square]
  rw [← tangentModelEquiv_apply, ← tangentModelEquiv_apply]
  change threeSignDirection x y (tangentModelEquiv v) =
    tangentModelEquiv (tangentModelEquiv.symm (threeSignDirection x y (tangentModelEquiv v)))
  exact (tangentModelEquiv.apply_symm_apply _).symm

theorem sign_polynomial_differential_comparison (x y : Bool)
    (v : SphereCenteredCoordinates.Tangent rotatedInput) :
    sphereSymmetricDifferential (signSphere x y rotatedInput)
        (signTangentEquiv x y rotatedInput v) =
      sphereSymmetricDifferential rotatedInput (signTangentComparison x y v) := by
  ext r s
  rw [sphereDiagonalDifferential_reconstruction (signSphere x y rotatedInput) diagonalPhases
      (signInput_diagonal_phase_square x y),
    sphereDiagonalDifferential_reconstruction rotatedInput diagonalPhases
      symmetricMap_rotatedInput_phase_square,
    sign_tangent_model_comparison]

end MidpointSeed
end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
