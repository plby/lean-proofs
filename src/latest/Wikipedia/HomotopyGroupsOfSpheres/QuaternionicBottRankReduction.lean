import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrixRotation
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnAction
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnFiber

/-!
# Explicit rank reduction for the quaternionic Bott matrix

Every off-diagonal entry of the raw Bott matrix has zero real part. Swapping
the first two rows therefore puts its first column inside one fixed section
chart. The section then reduces the matrix to Sp(2), continuously in all
parameters. The stabilization identity below is an actual matrix equality;
the homotopy comparison is not assumed here.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices QuaternionicColumns

local notation "ℍ" => Quaternion ℝ

def swapMatrix : Matrix (Fin 3) (Fin 3) ℍ := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem swapMatrix_star : star swapMatrix = swapMatrix := by
  apply Matrix.ext
  intro r s
  fin_cases r <;> fin_cases s <;> norm_num [swapMatrix, Matrix.star_apply, Matrix.cons_val_two]

theorem swapMatrix_square : swapMatrix * swapMatrix = 1 := by
  apply Matrix.ext
  intro r s
  fin_cases r <;> fin_cases s <;>
    norm_num [swapMatrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]

def swap : SpGroup (Fin 3) :=
  ⟨swapMatrix, by constructor <;> rw [swapMatrix_star, swapMatrix_square]⟩

theorem swap_mul_first_row (A : SpGroup (Fin 3)) (s : Fin 3) :
    (swap * A).val 0 s = A.val 1 s := by
  change (swapMatrix * A.val) 0 s = A.val 1 s
  simp [swapMatrix, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]

abbrev ReductionDomain := {A : SpGroup (Fin 3) // A.val 1 0 ≠ -1}

def reductionColumn (A : ReductionDomain) : columnChart (0 : Fin 3) :=
  ⟨column 0 (swap * A.val), by
    change (swap * A.val).val 0 0 ≠ -1
    rw [swap_mul_first_row]
    exact A.property⟩

theorem continuous_reductionColumn : Continuous reductionColumn := by
  apply Continuous.subtype_mk
  exact (column (0 : Fin 3)).continuous.comp (continuous_const.mul continuous_subtype_val)

def reductionSection (A : ReductionDomain) : SpGroup (Fin 3) := sectionMap 0 (reductionColumn A)

theorem continuous_reductionSection : Continuous reductionSection :=
  (continuous_sectionMap 0).comp continuous_reductionColumn

def reductionFiber (A : ReductionDomain) : AxisFiber 2 :=
  ⟨(reductionSection A)⁻¹ * (swap * A.val), by
    apply (column_inv_mul_eq_axis_iff 0 _ _).mpr
    exact column_sectionMap 0 (reductionColumn A)⟩

theorem continuous_reductionFiber : Continuous reductionFiber := by
  apply Continuous.subtype_mk
  exact continuous_reductionSection.inv.mul (continuous_const.mul continuous_subtype_val)

def reduce : C(ReductionDomain, SpGroup (Fin 2)) :=
  ⟨fun A ↦ lower (reductionFiber A), continuous_lower.comp continuous_reductionFiber⟩

theorem stabilization_reduce (A : ReductionDomain) :
    stabilization 2 (reduce A) = (reductionSection A)⁻¹ * (swap * A.val) :=
  stabilization_lower (reductionFiber A)

theorem rotation_offDiagonal_re {N : Type*} [Fintype N] [DecidableEq N]
    (s t : ℝ) (B : Space N) (r q : N) (hrq : r ≠ q) :
    ((rotation s t B).val r q).re = 0 := by
  rw [rotation_val, matrix_apply]
  simp only [if_neg hrq, smul_zero, zero_add, QuaternionicComplexPlane.embed_eq_mk]
  change (Real.sin s * Real.sin t) * 0 = 0
  exact mul_zero _

def rotationInDomain : C((ℝ × ℝ) × Space (Fin 3), ReductionDomain) where
  toFun z := ⟨rotation z.1.1 z.1.2 z.2, by
    intro he
    have hr := rotation_offDiagonal_re z.1.1 z.1.2 z.2 (1 : Fin 3) 0 (by decide)
    rw [he] at hr
    change (-1 : ℝ) = 0 at hr
    norm_num at hr⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_rotation

def reducedRotation : C((ℝ × ℝ) × Space (Fin 3), SpGroup (Fin 2)) :=
  reduce.comp rotationInDomain

theorem reducedRotation_stabilization (s t : ℝ) (B : Space (Fin 3)) :
    stabilization 2 (reducedRotation ((s, t), B)) =
      (reductionSection (rotationInDomain ((s, t), B)))⁻¹ * (swap * rotation s t B) :=
  stabilization_reduce _

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
