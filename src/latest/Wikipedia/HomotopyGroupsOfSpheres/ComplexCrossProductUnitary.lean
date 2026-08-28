import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryCongruence
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The explicit complex cross-product map into SU(3)

The polynomial matrix `z zᵀ + cross(conj z)` is unitary with determinant one
on the complex unit five-sphere. Its product with its transpose supplies a
concrete map into the symmetric unitary parameter space of the Bott family.
No claim about its homotopy class is assumed in these constructions.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicSymmetricMatrices

abbrev Vector := Fin 3 → ℂ
abbrev UnitSphere := Metric.sphere (0 : EuclideanSpace ℂ (Fin 3)) 1

def crossMatrix (z : Vector) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, -z 2, z 1; z 2, 0, -z 0; -z 1, z 0, 0]

def outer (z w : Vector) : Matrix (Fin 3) (Fin 3) ℂ := fun r s ↦ z r * w s

def matrix (z : Vector) : Matrix (Fin 3) (Fin 3) ℂ :=
  outer z z + crossMatrix (fun r ↦ star (z r))

def normPolynomial (z : Vector) : ℂ := ∑ r, star (z r) * z r

theorem matrix_mul_star (z : Vector) :
    matrix z * star (matrix z) =
      (normPolynomial z - 1) •
        outer z (fun r ↦ star (z r)) +
        normPolynomial z • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  apply Matrix.ext
  intro r s
  fin_cases r <;> fin_cases s <;>
    simp [matrix, outer, crossMatrix, normPolynomial, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.star_apply, star_add, star_mul] <;> ring

theorem matrix_det (z : Vector) : (matrix z).det = normPolynomial z ^ 2 := by
  simp [Matrix.det_fin_three, matrix, outer, crossMatrix, normPolynomial, Fin.sum_univ_three]
  ring

theorem normPolynomial_unit (z : UnitSphere) : normPolynomial z.val = 1 := by
  have hn : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
  have hi := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) z.val
  rw [EuclideanSpace.inner_eq_star_dotProduct, hn] at hi
  simpa [normPolynomial, dotProduct, mul_comm] using hi

theorem matrix_unitary (z : UnitSphere) : matrix z.val ∈ unitary (Matrix (Fin 3) (Fin 3) ℂ) := by
  have hr : matrix z.val * star (matrix z.val) = 1 := by
    rw [matrix_mul_star, normPolynomial_unit, sub_self, zero_smul, one_smul, zero_add]
  exact ⟨mul_eq_one_comm.mp hr, hr⟩

theorem matrix_unit_det (z : UnitSphere) : (matrix z.val).det = 1 := by
  rw [matrix_det, normPolynomial_unit, one_pow]

theorem continuous_matrix : Continuous matrix := by
  apply _root_.continuous_matrix
  intro r s
  fin_cases r <;> fin_cases s <;>
    simp only [matrix, outer, crossMatrix, Matrix.add_apply] <;> fun_prop

@[irreducible] def unitaryMap : C(UnitSphere, unitary (Matrix (Fin 3) (Fin 3) ℂ)) where
  toFun z := ⟨matrix z.val, matrix_unitary z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_matrix.comp
      ((PiLp.continuous_ofLp 2 (fun _ : Fin 3 ↦ ℂ)).comp continuous_subtype_val)

theorem unitaryMap_val (z : UnitSphere) : (unitaryMap z).val = matrix z.val := by
  unfold unitaryMap
  rfl

private def symmetricProjection {N : Type*} [Fintype N] [DecidableEq N] :
    C(unitary (Matrix N N ℂ), Space N) where
  toFun U := congruence U identity
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    change Continuous (fun U : unitary (Matrix N N ℂ) ↦ U.val * 1 * U.val.transpose)
    have hU : Continuous (fun U : unitary (Matrix N N ℂ) ↦ U.val) := continuous_subtype_val
    exact (hU.mul continuous_const).mul hU.matrix_transpose

def symmetricMap : C(UnitSphere, Space (Fin 3)) := symmetricProjection.comp unitaryMap

theorem symmetricMap_val (z : UnitSphere) :
    (symmetricMap z).val.val = matrix z.val * (matrix z.val).transpose := by
  change (unitaryMap z).val * 1 * (unitaryMap z).val.transpose = _
  rw [unitaryMap_val, mul_one]

theorem symmetricMap_det (z : UnitSphere) : (symmetricMap z).val.val.det = 1 := by
  rw [symmetricMap_val, Matrix.det_mul, Matrix.det_transpose, matrix_unit_det, one_mul]

def axis : UnitSphere :=
  ⟨EuclideanSpace.basisFun (Fin 3) ℂ 0, mem_sphere_zero_iff_norm.mpr
    ((EuclideanSpace.basisFun (Fin 3) ℂ).orthonormal.1 0)⟩

theorem axis_val : (fun r ↦ axis.val r) = ![1, 0, 0] := by
  funext r
  fin_cases r <;> simp [axis, EuclideanSpace.basisFun_apply]

theorem symmetricMap_axis : symmetricMap axis = identity := by
  apply Subtype.ext
  apply Subtype.ext
  rw [symmetricMap_val]
  change matrix (fun r ↦ axis.val r) * (matrix (fun r ↦ axis.val r)).transpose = 1
  rw [axis_val]
  apply Matrix.ext
  intro r s
  fin_cases r <;> fin_cases s <;>
    norm_num [matrix, outer, crossMatrix, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_two]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
