/- Adapted from the checked repository proof in Erdos1148/NormalizedAction.lean. -/
import ErdosProblems.Erdos941.PairLocal.FrameCongruence

/-!
# The normalized action of invertible two-by-two matrices

Dividing the change-of-variables action by the determinant yields a
determinant-one isometry of the ternary discriminant form. This is the
matrix realization used for local neighbors and for comparison with the
special-linear action.
-/

namespace Erdos941.PairLocal

def transformMatrix {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 3) (Fin 3) R :=
  !![M 0 0 ^ 2, M 0 0 * M 1 0, M 1 0 ^ 2;
     2 * M 0 0 * M 0 1, M 0 0 * M 1 1 + M 0 1 * M 1 0, 2 * M 1 0 * M 1 1;
     M 0 1 ^ 2, M 0 1 * M 1 1, M 1 1 ^ 2]

lemma coeffMatrixMap_transformMatrix {R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (t : R × R × R) :
    coeffMatrixMap (transformMatrix M) t = transform M t := by
  ext <;> simp [coeffMatrixMap, coeffVecEquiv_apply, coeffVecEquiv_symm_apply,
    Matrix.toLin'_apply, transformMatrix, transform] <;> ring

lemma det_transformMatrix {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    (transformMatrix M).det = M.det ^ 3 := by
  simp [transformMatrix, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

lemma coeffMatrixMap_smul {R : Type*} [CommRing R]
    (a : R) (M : Matrix (Fin 3) (Fin 3) R) (t : R × R × R) :
    coeffMatrixMap (a • M) t = a • coeffMatrixMap M t := by
  simp [coeffMatrixMap]

def normalizedTransformMatrix {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin 3) (Fin 3) K := M.det⁻¹ • transformMatrix M

lemma det_normalizedTransformMatrix {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) :
    (normalizedTransformMatrix M).det = 1 := by
  rw [normalizedTransformMatrix, Matrix.det_smul, det_transformMatrix, Fintype.card_fin,
    inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hM)]

lemma coeffMatrixMap_normalizedTransformMatrix {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (t : K × K × K) :
    coeffMatrixMap (normalizedTransformMatrix M) t = M.det⁻¹ • transform M t := by
  rw [normalizedTransformMatrix, coeffMatrixMap_smul, coeffMatrixMap_transformMatrix]

lemma discr_normalizedTransformMatrix {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) (t : K × K × K) :
    discr (coeffMatrixMap (normalizedTransformMatrix M) t) = discr t := by
  rw [coeffMatrixMap_normalizedTransformMatrix, discr_smul, discr_transform,
    ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hM), one_mul]

noncomputable def normalizedTransformIsometry {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) : specialDiscrGroup K := by
  have hdet := det_normalizedTransformMatrix M hM
  have hunit : IsUnit (normalizedTransformMatrix M).det := by rw [hdet]; exact isUnit_one
  refine ⟨coeffMatrixEquiv (normalizedTransformMatrix M) hunit, ?_, ?_⟩
  · intro t
    rw [coeffMatrixEquiv_apply]
    exact discr_normalizedTransformMatrix M hM t
  · rw [coeffMatrixEquiv_toLinearMap, det_coeffMatrixMap, hdet]

lemma normalizedTransformIsometry_apply {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) (t : K × K × K) :
    (normalizedTransformIsometry M hM).1 t = M.det⁻¹ • transform M t := by
  change coeffMatrixEquiv (normalizedTransformMatrix M) _ t = _
  rw [coeffMatrixEquiv_apply, coeffMatrixMap_normalizedTransformMatrix]

lemma transform_smul_matrix {R : Type*} [CommRing R] (c : R)
    (M : Matrix (Fin 2) (Fin 2) R) (t : R × R × R) :
    transform (c • M) t = c ^ 2 • transform M t := by
  ext <;> dsimp [transform] <;> ring

/-- Multiplying the representing matrix by a nonzero scalar does not change the action. -/
lemma normalizedTransformIsometry_smul {K : Type*} [Field K]
    (M : Matrix (Fin 2) (Fin 2) K) (hM : M.det ≠ 0) (c : K) (hc : c ≠ 0)
    (hCM : (c • M).det ≠ 0) :
    normalizedTransformIsometry (c • M) hCM = normalizedTransformIsometry M hM := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro t
  rw [normalizedTransformIsometry_apply, normalizedTransformIsometry_apply,
    transform_smul_matrix, Matrix.det_smul, Fintype.card_fin, smul_smul]
  congr 1
  field_simp

end Erdos941.PairLocal
