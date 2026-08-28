import Wikipedia.HopfProblem.DegreeCollapsePrimitiveRowReduction
import Wikipedia.HopfProblem.DegreeCollapseCanonicalMiddleMatrix

/-!
# Primitive integral functionals on the actual class columns

A surjective class-coordinate matrix and a primitive integral functional
give a surjective integer row. Exact matrix multiplication in transported
bases gives the same multiplication on the actual functional values.
-/

noncomputable section

open Function
open scoped BigOperators

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {H K : Type} [AddCommGroup H] [Module ℤ H] [AddCommGroup K] [Module ℤ K]
  {r n : ℕ}

theorem functional_class_row_surjective
    (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (v : Fin n → H)
    (hA : Surjective (classCoordinateMatrix B v).mulVec)
    (L : H →ₗ[ℤ] ℤ) (hL : Surjective L) :
    Surjective (Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j))).mulVec := by
  intro y
  obtain ⟨h, hh⟩ := hL (y 0)
  obtain ⟨x, hx⟩ := hA (B.symm h)
  have hsum : (∑ j, x j • v j) = h := by
    rw [← classCoordinateMatrix_mulVec B v x, hx, LinearEquiv.apply_symm_apply]
  refine ⟨x, ?_⟩
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have heq := congrArg L hsum
  rw [map_sum] at heq
  simp only [map_zsmul, smul_eq_mul] at heq
  change ∑ j, L (v j) * x j = y 0
  rw [← hh, ← heq]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

theorem transported_classes_of_matrix_product
    (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (e : H ≃ₗ[ℤ] K)
    (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : classCoordinateMatrix (B.trans e) w = classCoordinateMatrix B v * P)
    (j : Fin n) : e.symm (w j) = ∑ i, P i j • v i := by
  have hvec : (classCoordinateMatrix B v).mulVec (fun i => P i j) =
      (B.trans e).symm (w j) := by
    funext i
    exact (congrFun (congrFun hmatrix i) j).symm
  calc
    e.symm (w j) = B ((classCoordinateMatrix B v).mulVec (fun i => P i j)) := by
      rw [hvec]
      exact (B.apply_symm_apply (e.symm (w j))).symm
    _ = _ := classCoordinateMatrix_mulVec B v _

theorem functional_rows_of_matrix_product
    (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (e : H ≃ₗ[ℤ] K)
    (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : classCoordinateMatrix (B.trans e) w = classCoordinateMatrix B v * P)
    (L : H →ₗ[ℤ] ℤ) :
    Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (e.symm (w j))) =
      Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j)) * P := by
  funext u j
  change L (e.symm (w j)) = ∑ i, L (v i) * P i j
  rw [transported_classes_of_matrix_product B e v w P hmatrix j, map_sum]
  simp only [map_zsmul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
