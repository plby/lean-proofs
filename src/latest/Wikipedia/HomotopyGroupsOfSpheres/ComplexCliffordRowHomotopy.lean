import Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordRankReduction
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryProjection

/-! # A based symmetric homotopy for the Clifford row interchange -/

noncomputable section

open scoped Matrix unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

def rowRotationMatrix (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, Real.cos θ, -Real.sin θ;
     0, 0, Real.sin θ, Real.cos θ]

theorem rowRotationMatrix_unitary (θ : ℝ) :
    rowRotationMatrix θ ∈ unitary (Matrix (Fin 4) (Fin 4) ℂ) := by
  have hsq : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  have h : rowRotationMatrix θ * star (rowRotationMatrix θ) = 1 := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [rowRotationMatrix, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_succ,
        Matrix.cons_val_two, Matrix.cons_val_three, -Complex.ofReal_sin, -Complex.ofReal_cos] <;>
      ring_nf at hsq ⊢ <;> exact hsq
  exact ⟨mul_eq_one_comm.mp h, h⟩

def rowRotation : C(ℝ, unitary (Matrix (Fin 4) (Fin 4) ℂ)) where
  toFun θ := ⟨rowRotationMatrix θ, rowRotationMatrix_unitary θ⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply _root_.continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [rowRotationMatrix] <;> fun_prop

theorem rowRotation_zero : rowRotation 0 = 1 := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rowRotation, rowRotationMatrix, Matrix.cons_val_two, Matrix.cons_val_three]

theorem rowRotation_half_pi : rowRotation (Real.pi / 2) = rowSwap := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rowRotation, rowRotationMatrix, rowSwap, rowSwapMatrix,
      Matrix.cons_val_two, Matrix.cons_val_three]

theorem rowRotation_real (θ : ℝ) (i j : Fin 4) :
    star ((rowRotation θ).val i j) = (rowRotation θ).val i j := by
  fin_cases i <;> fin_cases j <;>
    simp [rowRotation, rowRotationMatrix, Matrix.cons_val_two, Matrix.cons_val_three,
      -Complex.ofReal_sin, -Complex.ofReal_cos]

def swappedFinMap : C(UnitSphere, unitary (Matrix (Fin 4) (Fin 4) ℂ)) :=
  ContinuousMap.const _ rowSwap * unitaryMap

def rowHomotopy : unitaryMap.Homotopy swappedFinMap where
  toFun p := rowRotation ((p.1 : ℝ) * (Real.pi / 2)) * unitaryMap p.2
  continuous_toFun :=
    (rowRotation.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).mul_const _)).mul
        (unitaryMap.continuous.comp continuous_snd)
  map_zero_left z := by
    change rowRotation ((0 : ℝ) * (Real.pi / 2)) * unitaryMap z = unitaryMap z
    rw [zero_mul, rowRotation_zero, one_mul]
  map_one_left z := by
    change rowRotation ((1 : ℝ) * (Real.pi / 2)) * unitaryMap z = rowSwap * unitaryMap z
    rw [one_mul, rowRotation_half_pi]

theorem rowHomotopy_axis_real (t : I) (i j : Fin 4) :
    star ((rowHomotopy (t, axis)).val i j) = (rowHomotopy (t, axis)).val i j := by
  change star ((rowRotation ((t : ℝ) * (Real.pi / 2)) * unitaryMap axis).val i j) =
    (rowRotation ((t : ℝ) * (Real.pi / 2)) * unitaryMap axis).val i j
  simp only [unitaryMap_axis, mul_one]
  exact rowRotation_real _ i j

def symmetricRowHomotopy :
    (unitaryProjection.comp unitaryMap).HomotopyRel
      (unitaryProjection.comp swappedFinMap) {axis} :=
  unitaryProjectionHomotopyRel rowHomotopy axis rowHomotopy_axis_real

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCliffordFive
