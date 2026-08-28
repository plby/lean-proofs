import Mathlib.Analysis.Quaternion
import Mathlib.Tactic.NormNum

/-! # Fixed imaginary quaternionic scalars for the symplectic spectral construction -/

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicScalars

open scoped Quaternion

def i : ℍ := ⟨0, 1, 0, 0⟩
def j : ℍ := ⟨0, 0, 1, 0⟩
def k : ℍ := ⟨0, 0, 0, 1⟩

@[simp] theorem i_mul_i : i * i = -1 := by
  have h : (QuaternionAlgebra.mk 0 1 0 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
    QuaternionAlgebra.mk 0 1 0 0 = -1 := by ext <;> norm_num
  exact h
@[simp] theorem j_mul_j : j * j = -1 := by
  have h : (QuaternionAlgebra.mk 0 0 1 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
    QuaternionAlgebra.mk 0 0 1 0 = -1 := by ext <;> norm_num
  exact h
@[simp] theorem k_mul_k : k * k = -1 := by
  have h : (QuaternionAlgebra.mk 0 0 0 1 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
    QuaternionAlgebra.mk 0 0 0 1 = -1 := by ext <;> norm_num
  exact h
@[simp] theorem i_mul_j : i * j = k := by
  have h : (QuaternionAlgebra.mk 0 1 0 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
    QuaternionAlgebra.mk 0 0 1 0 = QuaternionAlgebra.mk 0 0 0 1 := by ext <;> norm_num
  exact h
@[simp] theorem j_mul_i : j * i = -k := by
  have h : (QuaternionAlgebra.mk 0 0 1 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) *
    QuaternionAlgebra.mk 0 1 0 0 = -QuaternionAlgebra.mk 0 0 0 1 := by ext <;> norm_num
  exact h
@[simp] theorem star_i : star i = -i := by
  have h : star (QuaternionAlgebra.mk 0 1 0 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) =
    -QuaternionAlgebra.mk 0 1 0 0 := by ext <;> norm_num
  exact h
@[simp] theorem star_j : star j = -j := by
  have h : star (QuaternionAlgebra.mk 0 0 1 0 : QuaternionAlgebra ℝ (-1) 0 (-1)) =
    -QuaternionAlgebra.mk 0 0 1 0 := by ext <;> norm_num
  exact h
@[simp] theorem star_k : star k = -k := by
  have h : star (QuaternionAlgebra.mk 0 0 0 1 : QuaternionAlgebra ℝ (-1) 0 (-1)) =
    -QuaternionAlgebra.mk 0 0 0 1 := by ext <;> norm_num
  exact h

theorem i_mul_j_eq_neg_j_mul_i : i * j = -(j * i) := by
  rw [i_mul_j, j_mul_i, neg_neg]

theorem i_ne_zero : i ≠ 0 := by
  intro h
  have := congrArg QuaternionAlgebra.imI h
  change (1 : ℝ) = 0 at this
  exact one_ne_zero this

theorem j_ne_zero : j ≠ 0 := by
  intro h
  have := congrArg QuaternionAlgebra.imJ h
  change (1 : ℝ) = 0 at this
  exact one_ne_zero this

theorem norm_eq_one_of_square {q : ℍ} (hq : q * q = -1) : ‖q‖ = 1 := by
  have h : ‖q‖ * ‖q‖ = 1 := by rw [← norm_mul, hq, norm_neg, norm_one]
  nlinarith [norm_nonneg q]

@[simp] theorem norm_i : ‖i‖ = 1 := norm_eq_one_of_square i_mul_i
@[simp] theorem norm_j : ‖j‖ = 1 := norm_eq_one_of_square j_mul_j
@[simp] theorem norm_k : ‖k‖ = 1 := norm_eq_one_of_square k_mul_k

theorem scalar_commutator_ij (a b c : ℝ) :
    (a • i) * (c • j) - (c • j) * (b • i) = ((a + b) * c) • k := by
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, i_mul_j, j_mul_i,
    smul_neg, sub_neg_eq_add, ← add_smul]
  congr 1
  ring

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicScalars
