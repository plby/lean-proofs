import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointTrace

/-!
# A real rotation diagonalizing the midpoint target

The coordinate change is an involution of the unit five-sphere and
intertwines the explicit cross-product matrix and symmetric matrix maps.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

def rotationScale : ℂ := (Real.sqrt 2 : ℂ) / 2

theorem rotationScale_star : star rotationScale = rotationScale := by simp [rotationScale]

theorem rotationScale_conj : (starRingEnd ℂ) rotationScale = rotationScale := rotationScale_star

theorem rotationScale_sq : rotationScale ^ 2 = 1 / 2 := by
  have hs : ((Real.sqrt (2 : ℝ) : ℂ)) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  norm_num [rotationScale, div_pow, hs]

def targetRotation : Matrix (Fin 3) (Fin 3) ℂ :=
  !![rotationScale, 0, rotationScale; 0, -1, 0; rotationScale, 0, -rotationScale]

theorem targetRotation_transpose : targetRotation.transpose = targetRotation := by
  ext r s
  fin_cases r <;> fin_cases s <;> rfl

theorem targetRotation_mul_self : targetRotation * targetRotation = 1 := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [targetRotation, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two] <;>
    ring_nf <;> norm_num [rotationScale_sq]

theorem targetRotation_det : targetRotation.det = 1 := by
  simp [targetRotation, Matrix.det_fin_three]
  ring_nf
  norm_num [rotationScale_sq]

theorem matrix_targetRotation (z : Vector) :
    matrix (targetRotation *ᵥ z) = targetRotation * matrix z * targetRotation := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [matrix, outer, crossMatrix, targetRotation, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two, rotationScale_conj] <;>
    ring_nf <;> norm_num [rotationScale_sq] <;> ring

theorem normPolynomial_targetRotation (z : Vector) :
    normPolynomial (targetRotation *ᵥ z) = normPolynomial z := by
  simp [normPolynomial, targetRotation, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two, rotationScale_conj]
  ring_nf
  norm_num [rotationScale_sq]
  ring

theorem squareSum_targetRotation (z : Vector) : squareSum (targetRotation *ᵥ z) = squareSum z := by
  simp [squareSum, targetRotation, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Matrix.cons_val_two]
  ring_nf
  norm_num [rotationScale_sq]
  ring

theorem normPolynomial_eq_norm_sq (z : EuclideanSpace ℂ (Fin 3)) :
    normPolynomial z = (‖z‖ ^ 2 : ℝ) := by
  have hi := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hi
  simpa [normPolynomial, dotProduct, mul_comm] using hi

def rotationSphere (z : UnitSphere) : UnitSphere :=
  ⟨WithLp.toLp 2 (targetRotation *ᵥ z.val), by
    apply mem_sphere_zero_iff_norm.mpr
    have hn : normPolynomial (targetRotation *ᵥ z.val) = 1 := by
      rw [normPolynomial_targetRotation, normPolynomial_unit]
    have he := normPolynomial_eq_norm_sq (WithLp.toLp 2 (targetRotation *ᵥ z.val))
    change normPolynomial (targetRotation *ᵥ z.val) = _ at he
    rw [hn] at he
    have hs : ‖WithLp.toLp 2 (targetRotation *ᵥ z.val)‖ ^ 2 = (1 : ℝ) := by
      exact_mod_cast he.symm
    nlinarith [norm_nonneg (WithLp.toLp 2 (targetRotation *ᵥ z.val))]⟩

theorem rotationSphere_val (z : UnitSphere) :
    (fun r ↦ (rotationSphere z).val r) = targetRotation *ᵥ z.val := rfl

theorem rotationSphere_involutive : Function.Involutive rotationSphere := by
  intro z
  apply Subtype.ext
  ext r
  change (targetRotation *ᵥ (targetRotation *ᵥ z.val)) r = z.val r
  rw [Matrix.mulVec_mulVec, targetRotation_mul_self, Matrix.one_mulVec]

theorem symmetricMap_rotationSphere (z : UnitSphere) :
    (symmetricMap (rotationSphere z)).val.val =
      targetRotation * (symmetricMap z).val.val * targetRotation := by
  rw [symmetricMap_val, symmetricMap_val]
  change matrix (targetRotation *ᵥ z.val) * (matrix (targetRotation *ᵥ z.val)).transpose = _
  rw [matrix_targetRotation, Matrix.transpose_mul, Matrix.transpose_mul, targetRotation_transpose]
  simp only [mul_assoc, ← mul_assoc targetRotation targetRotation, targetRotation_mul_self, one_mul]

theorem targetRotation_targetMatrix (α β : ℂ) :
    targetRotation * targetMatrix α β * targetRotation = Matrix.diagonal ![α + β, 1, α - β] := by
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [targetRotation, targetMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_two] <;>
    ring_nf <;> norm_num [rotationScale_sq] <;> ring

def targetEigenvalues : Fin 3 → ℂ := ![targetAlpha + targetBeta, 1, targetAlpha - targetBeta]

theorem midpoint_diagonalized (z : UnitSphere) (u : ℂ)
    (hB : (symmetricMap z).val.val = u • targetMatrix targetAlpha targetBeta) :
    (symmetricMap (rotationSphere z)).val.val =
      Matrix.diagonal (fun r ↦ u * targetEigenvalues r) := by
  rw [symmetricMap_rotationSphere, hB, Matrix.mul_smul, Matrix.smul_mul,
    targetRotation_targetMatrix]
  ext r s
  by_cases h : r = s
  · subst s
    simp [targetEigenvalues]
  · simp [h]

theorem midpoint_rotated_squareSum (z : UnitSphere) (u : unitary ℂ) (hu : u.val ^ 3 = -1)
    (hB : (symmetricMap z).val.val = u.val • targetMatrix targetAlpha targetBeta) :
    squareSum (rotationSphere z).val = -star u.val * traceRoot := by
  change squareSum (targetRotation *ᵥ z.val) = _
  rw [squareSum_targetRotation, midpoint_squareSum z u hu hB]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
