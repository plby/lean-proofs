import Wikipedia.HomotopyGroupsOfSpheres.UnitaryZeroCornerHomotopy

/-!
# The explicit Clifford matrix on the complex unit five-sphere

This constructs the actual four-by-four matrix and its continuous unitary
family. Its homotopy class is not assumed to generate.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open ComplexCrossProductUnitary

def matrix (z : Vector) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![z 0, 0, -star (z 1), -star (z 2);
     0, z 0, z 2, -z 1;
     z 1, -star (z 2), star (z 0), 0;
     z 2, star (z 1), 0, star (z 0)]

theorem matrix_mul_star (z : Vector) :
    matrix z * star (matrix z) = normPolynomial z • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Matrix.star_apply, normPolynomial, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

theorem matrix_unitary (z : UnitSphere) :
    matrix z.val ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ) := by
  have hr : matrix z.val * star (matrix z.val) = 1 := by
    rw [matrix_mul_star, normPolynomial_unit, one_smul]
  exact ⟨mul_eq_one_comm.mp hr, hr⟩

theorem continuous_matrix : Continuous matrix := by
  apply _root_.continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [matrix] <;> fun_prop

def unitaryMap : C(UnitSphere, unitary (Matrix (Fin 4) (Fin 4) ℂ)) where
  toFun z := ⟨matrix z.val, matrix_unitary z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_matrix.comp
      ((PiLp.continuous_ofLp 2 (fun _ : Fin 3 ↦ ℂ)).comp continuous_subtype_val)

theorem unitaryMap_val (z : UnitSphere) : (unitaryMap z).val = matrix z.val := rfl

theorem unitaryMap_axis : unitaryMap axis = 1 := by
  apply Subtype.ext
  change matrix (fun i ↦ axis.val i) = 1
  rw [axis_val]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, Matrix.cons_val_two, Matrix.cons_val_three]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
