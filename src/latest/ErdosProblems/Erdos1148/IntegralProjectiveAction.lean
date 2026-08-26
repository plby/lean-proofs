import ErdosProblems.Erdos1148.ProjectiveAction
import ErdosProblems.Erdos1148.PrimitiveMatrix
import ErdosProblems.Erdos1148.BaseChange

/-!
# Integral matrices representing special isometries

A rational matrix representing an integral special isometry can be scaled to
a primitive integral matrix. Its determinant divides all four squared entries,
so that determinant is a unit. This is the integral step in comparing the
special orthogonal and binary-form actions.
-/

namespace Erdos1148.DukeArithmetic

lemma matrix_normalizedTransformIsometry {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) :
    matrixOfCoeffMap (normalizedTransformIsometry M hM).1.toLinearMap =
      normalizedTransformMatrix M := by
  change matrixOfCoeffMap (coeffMatrixEquiv (normalizedTransformMatrix M) _).toLinearMap = _
  rw [coeffMatrixEquiv_toLinearMap, matrixOfCoeffMap_coeffMatrixMap]

def cornerIndex : Fin 2 → Fin 3 := ![0, 2]

lemma normalizedTransformMatrix_corner {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    normalizedTransformMatrix M (cornerIndex j) (cornerIndex i) = M.det⁻¹ * M i j ^ 2 := by
  fin_cases i <;> fin_cases j <;>
    simp [normalizedTransformMatrix, transformMatrix, cornerIndex]

lemma int_dvd_of_inv_mul_sq_eq {a D z : ℤ} (hD : D ≠ 0)
    (h : (D : ℚ)⁻¹ * (a : ℚ) ^ 2 = (z : ℚ)) : D ∣ a ^ 2 := by
  have hDQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have heq : (a : ℚ) ^ 2 = (D : ℚ) * z := by
    rw [← h, ← mul_assoc, mul_inv_cancel₀ hDQ, one_mul]
  exact ⟨z, by exact_mod_cast heq⟩

/-- An integral special isometry has a unimodular integral projective representative. -/
theorem exists_integral_normalizedTransformIsometry (g : specialDiscrGroup ℤ) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : IsUnit A.det),
      normalizedTransformIsometry (A.map (Int.castRingHom ℚ))
        (by
          change ((Int.castRingHom ℚ).mapMatrix A).det ≠ 0
          rw [← RingHom.map_det]
          exact (hA.map (Int.castRingHom ℚ)).ne_zero) =
        specialDiscrBaseChange (Int.castRingHom ℚ) g := by
  let φ := Int.castRingHom ℚ
  obtain ⟨M, hM, hg⟩ := exists_normalizedTransformIsometry (specialDiscrBaseChange φ g)
  obtain ⟨c, A, hc, hAM, hprim⟩ := exists_primitive_integer_matrix M hM
  have hAQ : (A.map φ).det ≠ 0 := by
    rw [hAM, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) hM
  have hA : A.det ≠ 0 := by
    intro hz
    apply hAQ
    change (φ.mapMatrix A).det = 0
    rw [← φ.map_det, hz, map_zero]
  have hnormalized : normalizedTransformIsometry (A.map φ) hAQ =
      specialDiscrBaseChange φ g := by
    calc
      normalizedTransformIsometry (A.map φ) hAQ =
          normalizedTransformIsometry (c • M) (by simpa only [← hAM] using hAQ) := by
            congr 1
      _ = normalizedTransformIsometry M hM := normalizedTransformIsometry_smul M hM c hc _
      _ = specialDiscrBaseChange φ g := hg
  have hmatrix : normalizedTransformMatrix (A.map φ) =
      (matrixOfCoeffMap g.1.toLinearMap).map φ := by
    rw [← matrix_normalizedTransformIsometry (A.map φ) hAQ, hnormalized,
      matrix_specialDiscrBaseChange]
  have hdiv (ij : Fin 2 × Fin 2) : A.det ∣ A ij.1 ij.2 ^ 2 := by
    have h := congrArg (fun N => N (cornerIndex ij.2) (cornerIndex ij.1)) hmatrix
    rw [normalizedTransformMatrix_corner] at h
    change (φ.mapMatrix A).det⁻¹ * φ (A ij.1 ij.2) ^ 2 =
      φ (matrixOfCoeffMap g.1.toLinearMap (cornerIndex ij.2) (cornerIndex ij.1)) at h
    rw [← φ.map_det] at h
    exact int_dvd_of_inv_mul_sq_eq hA h
  exact ⟨A, isUnit_of_dvd_squares_primitive _ _ hprim hdiv, hnormalized⟩

end Erdos1148.DukeArithmetic
