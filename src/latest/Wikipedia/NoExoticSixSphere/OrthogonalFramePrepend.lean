import Wikipedia.NoExoticSixSphere.GramSchmidtOrthogonalCons
import Wikipedia.HopfProblem.DegreeCollapseEuclideanProductCoordinates

/-!
# Prepending an orthogonal normal column in the actual ordered coordinates

The added column is first and the old columns keep their original order.
The complete normalized operator is computed from the proved ordered
Gram--Schmidt identities, including a positive scale on the new unit column.
-/

noncomputable section

open InnerProductSpace

namespace NoExoticSixSphere.OrthogonalFramePrepend

open GLOrthonormalization Stiefel

variable {N k : ℕ}

def operator (z : Vector N) (A : Vector k →L[ℝ] Vector N) :
    Vector (k + 1) →L[ℝ] Vector N :=
  (((ContinuousLinearMap.id ℝ ℝ).smulRight z).coprod A).comp
    (Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates k).symm.toContinuousLinearMap

theorem operator_apply (z : Vector N) (A : Vector k →L[ℝ] Vector N) (v : Vector (k + 1)) :
    operator z A v = v 0 • z + A (WithLp.toLp 2 (fun i : Fin k ↦ v i.succ)) := rfl

theorem headCoordinates_basis_zero (k : ℕ) :
    (Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates k).symm
      (EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0) = (1, 0) := by
  apply (Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates k).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates_head]
    simp [EuclideanSpace.basisFun_apply]
  · rw [Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates_tail]
    simp [EuclideanSpace.basisFun_apply]

theorem headCoordinates_basis_succ (k : ℕ) (i : Fin k) :
    (Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates k).symm
      (EuclideanSpace.basisFun (Fin (k + 1)) ℝ i.succ) =
        (0, EuclideanSpace.basisFun (Fin k) ℝ i) := by
  apply (Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates k).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext j
  refine Fin.cases ?_ (fun l ↦ ?_) j
  · rw [Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates_head]
    simp [EuclideanSpace.basisFun_apply]
  · rw [Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates_tail]
    simp [EuclideanSpace.basisFun_apply]

theorem operator_basis_zero (z : Vector N) (A : Vector k →L[ℝ] Vector N) :
    operator z A (EuclideanSpace.basisFun (Fin (k + 1)) ℝ 0) = z := by
  change (((ContinuousLinearMap.id ℝ ℝ).smulRight z).coprod A)
    ((Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates k).symm _) = z
  rw [headCoordinates_basis_zero]
  change (1 : ℝ) • z + A 0 = z
  rw [one_smul, map_zero, add_zero]

theorem operator_basis_succ (z : Vector N) (A : Vector k →L[ℝ] Vector N) (i : Fin k) :
    operator z A (EuclideanSpace.basisFun (Fin (k + 1)) ℝ i.succ) =
      A (EuclideanSpace.basisFun (Fin k) ℝ i) := by
  change (((ContinuousLinearMap.id ℝ ℝ).smulRight z).coprod A)
    ((Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.coordinates k).symm _) = _
  rw [headCoordinates_basis_succ]
  change (0 : ℝ) • z + A _ = _
  rw [zero_smul, zero_add]
  rfl

theorem columns_operator {X : Type*} (z : Vector N) (A : X → Vector k →L[ℝ] Vector N)
    (x : X) : Orthonormalization.columns (fun y ↦ operator z (A y)) x =
      Fin.cons z (Orthonormalization.columns A x) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact operator_basis_zero z (A x)
  · exact operator_basis_succ z (A x) j

theorem normalized_operator {X : Type*} (z : Vector N)
    (A : X → Vector k →L[ℝ] Vector N) (x : X) (hz : ∀ v, inner ℝ z (A x v) = 0) :
    Orthonormalization.operator (fun y ↦ operator z (A y)) x =
      operator (‖z‖⁻¹ • z) (Orthonormalization.operator A x) := by
  have he : (Orthonormalization.operator (fun y ↦ operator z (A y)) x).toLinearMap =
      (operator (‖z‖⁻¹ • z) (Orthonormalization.operator A x)).toLinearMap := by
    apply (EuclideanSpace.basisFun (Fin (k + 1)) ℝ).toBasis.ext
    intro i
    change Orthonormalization.linearMap (fun y ↦ operator z (A y)) x
      (EuclideanSpace.basisFun (Fin (k + 1)) ℝ i) =
        operator (‖z‖⁻¹ • z) (Orthonormalization.operator A x)
          (EuclideanSpace.basisFun (Fin (k + 1)) ℝ i)
    rw [Orthonormalization.linearMap_basis]
    change gramSchmidtNormed ℝ (Orthonormalization.columns (fun y ↦ operator z (A y)) x) i = _
    rw [columns_operator]
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [gramSchmidtNormed_fin_cons_zero, operator_basis_zero]
    · rw [gramSchmidtNormed_fin_cons_succ z (Orthonormalization.columns A x)
        (fun l ↦ hz (EuclideanSpace.basisFun (Fin k) ℝ l)), operator_basis_succ]
      exact (Orthonormalization.linearMap_basis A x j).symm
  exact ContinuousLinearMap.ext (fun v ↦
    congrArg (fun L : Vector (k + 1) →ₗ[ℝ] Vector N ↦ L v) he)

theorem normalized_operator_pos_smul {X : Type*} (z : Vector N) (hz : ‖z‖ = 1)
    (r : ℝ) (hr : 0 < r) (A : X → Vector k →L[ℝ] Vector N) (x : X)
    (ho : ∀ v, inner ℝ z (A x v) = 0) :
    Orthonormalization.operator (fun y ↦ operator (r • z) (A y)) x =
      operator z (Orthonormalization.operator A x) := by
  rw [normalized_operator (r • z) A x (fun v ↦ by
    rw [real_inner_smul_left, ho, mul_zero])]
  have hs : ‖r • z‖⁻¹ • (r • z) = z := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hz, mul_one, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  rw [hs]

end NoExoticSixSphere.OrthogonalFramePrepend
