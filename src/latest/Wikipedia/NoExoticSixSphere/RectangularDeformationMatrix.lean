import Wikipedia.NoExoticSixSphere.RectangularSmoothNormalization
import Wikipedia.NoExoticSixSphere.GLDeformation
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Injectivity throughout rectangular Gram--Schmidt interpolation

Test the interpolating operator against its actual normalized frame. The
resulting square matrix is upper triangular with strictly positive diagonal,
so the test operator is invertible and the original interpolation is injective.
-/

noncomputable section

open InnerProductSpace Module Function unitInterval

namespace NoExoticSixSphere.Stiefel.RectangularDeformation

open GLOrthonormalization

variable {X : Type*} {N n : ℕ}
  (A : X → Vector n →L[ℝ] Vector N) (hi : ∀ x, Injective (A x))

def interpolation (p : I × X) : Vector n →L[ℝ] Vector N :=
  (1 - (p.1 : ℝ)) • A p.2 + (p.1 : ℝ) • Orthonormalization.operator A p.2

def testOperator (p : I × X) : Vector n →L[ℝ] Vector n :=
  (Orthonormalization.operator A p.2).adjoint.comp (interpolation A p)

def matrix (p : I × X) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (testOperator A p).toLinearMap

theorem normalizedOperator_basis (x : X) (i : Fin n) :
    Orthonormalization.operator A x (EuclideanSpace.basisFun (Fin n) ℝ i) =
      Orthonormalization.normalized A x i :=
  Orthonormalization.linearMap_basis A x i

include hi in
theorem matrix_entry (p : I × X) (i j : Fin n) :
    matrix A p i j =
      (1 - (p.1 : ℝ)) * inner ℝ (Orthonormalization.normalized A p.2 i)
        (Orthonormalization.columns A p.2 j) +
      (p.1 : ℝ) * (if i = j then 1 else 0) := by
  rw [matrix, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  change inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)
    ((Orthonormalization.operator A p.2).adjoint
      (interpolation A p (EuclideanSpace.basisFun (Fin n) ℝ j))) = _
  rw [ContinuousLinearMap.adjoint_inner_right, normalizedOperator_basis]
  change inner ℝ (Orthonormalization.normalized A p.2 i)
    ((1 - (p.1 : ℝ)) • Orthonormalization.columns A p.2 j +
      (p.1 : ℝ) • Orthonormalization.operator A p.2
        (EuclideanSpace.basisFun (Fin n) ℝ j)) = _
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right,
    normalizedOperator_basis,
    (orthonormal_iff_ite.mp (Orthonormalization.normalized_orthonormal A hi p.2)) i j]

include hi in
theorem matrix_upper (p : I × X) : (matrix A p).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  have hz : inner ℝ (Orthonormalization.normalized A p.2 i)
      (Orthonormalization.columns A p.2 j) = 0 := by
    unfold Orthonormalization.normalized gramSchmidtNormed
    rw [real_inner_smul_left, gramSchmidt_inv_triangular ℝ _ hji, mul_zero]
  rw [matrix_entry A hi, hz, if_neg (ne_of_gt hji)]
  ring

include hi in
theorem matrix_diagonal_pos (p : I × X) (i : Fin n) : 0 < matrix A p i i := by
  rw [matrix_entry A hi, if_pos rfl, mul_one]
  have hd : 0 < inner ℝ (Orthonormalization.normalized A p.2 i)
      (Orthonormalization.columns A p.2 i) :=
    inner_gramSchmidtNormed_diagonal_pos (Orthonormalization.columns A p.2)
      (Orthonormalization.columns_independent A hi p.2) i
  by_cases ht : (p.1 : ℝ) = 1
  · simp only [ht, sub_self, zero_mul, zero_add, zero_lt_one]
  · have hlt : (p.1 : ℝ) < 1 := lt_of_le_of_ne p.1.property.2 ht
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) hd) p.1.property.1

include hi in
theorem matrix_det_pos (p : I × X) : 0 < (matrix A p).det := by
  rw [Matrix.det_of_isUpperTriangular (matrix_upper A hi p)]
  exact Finset.prod_pos (fun i _ ↦ matrix_diagonal_pos A hi p i)

include hi in
theorem testOperator_isInvertible (p : I × X) : (testOperator A p).IsInvertible := by
  have hdet : IsUnit (matrix A p).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (matrix_det_pos A hi p))
  refine ⟨(LinearEquiv.ofIsUnitDet hdet).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  rfl

include hi in
theorem injective_interpolation (p : I × X) : Injective (interpolation A p) := by
  intro v w hvw
  apply (testOperator_isInvertible A hi p).injective
  exact congrArg (Orthonormalization.operator A p.2).adjoint hvw

theorem interpolation_zero (x : X) : interpolation A (0, x) = A x := by
  simp [interpolation]

theorem interpolation_one (x : X) :
    interpolation A (1, x) = Orthonormalization.operator A x := by
  simp [interpolation]

end NoExoticSixSphere.Stiefel.RectangularDeformation
