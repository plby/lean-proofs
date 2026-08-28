import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductSignTangent

/-!
# The four actual symmetric-matrix families in one source coordinate space

The source chart is the explicit diagonal seed chart, followed by the chosen
sign isometry and the fixed real rotation. All four centers give the same
target matrix. Their derivatives are compared using the proved tangent map.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed

open QuaternionicBottMatrix QuaternionicSymmetricMatrices

def signParameterComparison (x y : Bool) :
    ParameterSpace rotatedInput →ₗ[ℝ] ParameterSpace rotatedInput :=
  LinearMap.prodMap LinearMap.id (LinearMap.prodMap LinearMap.id (signTangentComparison x y))

theorem signParameterComparison_det (x y : Bool) : (signParameterComparison x y).det = 1 := by
  rw [signParameterComparison, LinearMap.det_prodMap, LinearMap.det_prodMap,
    LinearMap.det_id, signTangentComparison_det]
  norm_num

def signMatrixFamily (x y : Bool) (p : ParameterSpace rotatedInput) : Space (Fin 3) :=
  symmetricMap (rotationSphere
    (signSphere x y (SphereCenteredCoordinates.inverse rotatedInput p.2.2)))

theorem signMatrixFamily_val (x y : Bool) (p : ParameterSpace rotatedInput) :
    (signMatrixFamily x y p).val.val =
      targetRotation * (signMatrix x y * sphereSymmetricChart rotatedInput p.2.2 *
        signMatrix x y) * targetRotation := by
  unfold signMatrixFamily sphereSymmetricChart
  rw [symmetricMap_rotationSphere, symmetricMap_signSphere]

theorem signMatrixFamily_zero (x y : Bool) :
    (signMatrixFamily x y 0).val.val = (-1 : ℂ) • targetMatrix targetAlpha targetBeta := by
  change (symmetricMap (rotationSphere
    (signSphere x y (SphereCenteredCoordinates.inverse rotatedInput 0)))).val.val = _
  rw [SphereCenteredCoordinates.inverse_zero]
  apply rotationSphere_target_of_diagonal
  simpa only [neg_one_mul] using
    diagonal_signSphere x y rotatedInput _ symmetricMap_rotatedInput

def signSphereInput (x y : Bool) : UnitSphere := rotationSphere (signSphere x y rotatedInput)

theorem phaseInput_eq_scalar_signSphereInput (u : unitary ℂ) (b : Bool × Bool) :
    phaseInput u b = scalarSphere (negativePhase u) (signSphereInput b.1 b.2) := by
  apply Subtype.ext
  apply PiLp.ext
  intro r
  change (targetRotation *ᵥ ((negativePhase u).val • signVector b.1 b.2 rotatedInput.val)) r =
    (negativePhase u).val * (targetRotation *ᵥ signVector b.1 b.2 rotatedInput.val) r
  rw [Matrix.mulVec_smul]
  rfl

def signMatrixVariation (x y : Bool) (v : ParameterSpace rotatedInput) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  targetRotation * (signMatrix x y * sphereSymmetricDifferential rotatedInput v.2.2 *
    signMatrix x y) * targetRotation

theorem hasDerivAt_signMatrixFamily_entry (x y : Bool) (v : ParameterSpace rotatedInput)
    (r s : Fin 3) :
    HasDerivAt (fun t : ℝ ↦ (signMatrixFamily x y (t • v)).val.val r s)
      (signMatrixVariation x y v r s) 0 := by
  have hS := hasDerivAt_matrix_congruence_entry
    (fun t : ℝ ↦ sphereSymmetricChart rotatedInput (t • v.2.2))
    (sphereSymmetricDifferential rotatedInput v.2.2) (signMatrix x y) (signMatrix x y) 0
    (sphereSymmetricDifferential_curve_entry rotatedInput v.2.2)
  have hR := hasDerivAt_matrix_congruence_entry
    (fun t : ℝ ↦ signMatrix x y * sphereSymmetricChart rotatedInput (t • v.2.2) * signMatrix x y)
    (signMatrix x y * sphereSymmetricDifferential rotatedInput v.2.2 * signMatrix x y)
    targetRotation targetRotation 0 hS r s
  have he : (fun t : ℝ ↦ (signMatrixFamily x y (t • v)).val.val r s) =
      fun t : ℝ ↦ (targetRotation * (signMatrix x y *
        sphereSymmetricChart rotatedInput (t • v.2.2) * signMatrix x y) * targetRotation) r s := by
    funext t
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ ↦ M r s) (signMatrixFamily_val x y (t • v))
  rw [he]
  exact hR

theorem signMatrix_true_true : signMatrix true true = 1 := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [signMatrix, signs, boolSign, Matrix.cons_val_two]

theorem signMatrixVariation_comparison (x y : Bool) (v : ParameterSpace rotatedInput) :
    signMatrixVariation x y v =
      signMatrixVariation true true (signParameterComparison x y v) := by
  have he := sign_polynomial_differential_comparison x y v.2.2
  rw [sphereSymmetricDifferential_sign] at he
  change targetRotation * (signMatrix x y * sphereSymmetricDifferential rotatedInput v.2.2 *
    signMatrix x y) * targetRotation =
      targetRotation * (signMatrix true true *
        sphereSymmetricDifferential rotatedInput (signTangentComparison x y v.2.2) *
          signMatrix true true) * targetRotation
  rw [he, signMatrix_true_true, one_mul, mul_one]

theorem contDiff_matrix_congruence_entry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} (A : E → Matrix (Fin 3) (Fin 3) ℂ)
    (P Q : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ r s, ContDiff ℝ n (fun p ↦ A p r s)) (r s : Fin 3) :
    ContDiff ℝ n (fun p ↦ (P * A p * Q) r s) := by
  have hP (k : Fin 3) : ContDiff ℝ n (fun p ↦ (P * A p) r k) := by
    change ContDiff ℝ n (fun p ↦ ∑ j : Fin 3, P r j * A p j k)
    exact ContDiff.sum (fun j _ ↦ contDiff_const.mul (hA j k))
  change ContDiff ℝ n (fun p ↦ ∑ k : Fin 3, (P * A p) r k * Q k s)
  exact ContDiff.sum (fun k _ ↦ (hP k).mul contDiff_const)

theorem contDiff_signMatrixFamily_entry (x y : Bool) {n : ℕ∞ω} (r s : Fin 3) :
    ContDiff ℝ n (fun p : ParameterSpace rotatedInput ↦ (signMatrixFamily x y p).val.val r s) := by
  have hA (j k : Fin 3) : ContDiff ℝ n (fun p : ParameterSpace rotatedInput ↦
      sphereSymmetricChart rotatedInput p.2.2 j k) :=
    (contDiff_symmetricMap_entry (SphereCenteredCoordinates.inverse rotatedInput)
      (contDiff_sphereInverse_entry rotatedInput) j k).comp contDiff_snd.snd
  have hS := contDiff_matrix_congruence_entry
    (fun p : ParameterSpace rotatedInput ↦ sphereSymmetricChart rotatedInput p.2.2)
    (signMatrix x y) (signMatrix x y) hA
  have hR := contDiff_matrix_congruence_entry
    (fun p : ParameterSpace rotatedInput ↦ signMatrix x y *
      sphereSymmetricChart rotatedInput p.2.2 * signMatrix x y)
    targetRotation targetRotation hS r s
  have he : (fun p : ParameterSpace rotatedInput ↦ (signMatrixFamily x y p).val.val r s) =
      fun p ↦ (targetRotation * (signMatrix x y * sphereSymmetricChart rotatedInput p.2.2 *
        signMatrix x y) * targetRotation) r s := by
    funext p
    exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ ↦ M r s) (signMatrixFamily_val x y p)
  rw [he]
  exact hR

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary.MidpointSeed
