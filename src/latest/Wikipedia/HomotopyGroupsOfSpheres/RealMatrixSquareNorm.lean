import Wikipedia.HomotopyGroupsOfSpheres.RealUnitaryMatrices
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # The matrix Hilbert--Schmidt square norm and orthogonal conjugation -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.RealMatrixSquareNorm

variable {N : Type*} [Fintype N]

def squareNorm (A : Matrix N N ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

theorem squareNorm_nonneg (A : Matrix N N ℝ) : 0 ≤ squareNorm A :=
  Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

@[simp] theorem squareNorm_zero : squareNorm (0 : Matrix N N ℝ) = 0 := by
  simp [squareNorm]

theorem entry_square_le (A : Matrix N N ℝ) (i j : N) : A i j ^ 2 ≤ squareNorm A := by
  apply le_trans (Finset.single_le_sum (fun k _ ↦ sq_nonneg (A i k)) (Finset.mem_univ j))
  exact Finset.single_le_sum
    (fun k _ ↦ Finset.sum_nonneg (fun l _ ↦ sq_nonneg (A k l))) (Finset.mem_univ i)

theorem squareNorm_eq_zero_iff (A : Matrix N N ℝ) : squareNorm A = 0 ↔ A = 0 := by
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    have he := entry_square_le A i j
    rw [h] at he
    change A i j = 0
    nlinarith [sq_nonneg (A i j)]
  · rintro rfl
    exact squareNorm_zero

theorem squareNorm_pos (A : Matrix N N ℝ) (hA : A ≠ 0) : 0 < squareNorm A := by
  apply lt_of_le_of_ne (squareNorm_nonneg A)
  intro h
  exact hA ((squareNorm_eq_zero_iff A).mp h.symm)

theorem squareNorm_eq_trace (A : Matrix N N ℝ) : squareNorm A = (A.transpose * A).trace := by
  change (∑ i, ∑ j, A i j ^ 2) = ∑ i, ∑ j, A j i * A j i
  rw [Finset.sum_comm]
  simp only [pow_two]

variable [DecidableEq N]

def conjugate (U : unitary (Matrix N N ℝ)) : Matrix N N ℝ →ₗ[ℝ] Matrix N N ℝ where
  toFun A := U.val * A * U.val.transpose
  map_add' A B := by rw [mul_add, add_mul]
  map_smul' c A := by rw [mul_smul_comm, smul_mul_assoc]; rfl

theorem transpose_mul_self (U : unitary (Matrix N N ℝ)) : U.val.transpose * U.val = 1 := by
  rw [← RealUnitaryMatrices.star_eq_transpose]
  exact Unitary.star_mul_self_of_mem U.property

theorem conjugate_mul (U : unitary (Matrix N N ℝ)) (A B : Matrix N N ℝ) :
    conjugate U A * conjugate U B = conjugate U (A * B) := by
  calc
    conjugate U A * conjugate U B =
        U.val * (A * (U.val.transpose * U.val) * B) * U.val.transpose := by
      simp only [conjugate, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
    _ = conjugate U (A * B) := by rw [transpose_mul_self, mul_one]; rfl

theorem conjugate_transpose (U : unitary (Matrix N N ℝ)) (A : Matrix N N ℝ) :
    (conjugate U A).transpose = conjugate U A.transpose := by
  change (U.val * A * U.val.transpose).transpose = U.val * A.transpose * U.val.transpose
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_mul, mul_assoc]

theorem trace_conjugate (U : unitary (Matrix N N ℝ)) (A : Matrix N N ℝ) :
    (conjugate U A).trace = A.trace := by
  change (U.val * A * U.val.transpose).trace = A.trace
  rw [Matrix.trace_mul_comm, ← mul_assoc, transpose_mul_self, one_mul]

theorem squareNorm_conjugate (U : unitary (Matrix N N ℝ)) (A : Matrix N N ℝ) :
    squareNorm (conjugate U A) = squareNorm A := by
  rw [squareNorm_eq_trace, conjugate_transpose, conjugate_mul, trace_conjugate,
    ← squareNorm_eq_trace]

theorem conjugate_injective (U : unitary (Matrix N N ℝ)) : Function.Injective (conjugate U) := by
  intro A B h
  have hz : squareNorm (A - B) = 0 := by
    rw [← squareNorm_conjugate U, map_sub, h, sub_self, squareNorm_zero]
  exact sub_eq_zero.mp ((squareNorm_eq_zero_iff _).mp hz)

def commutator (A B : Matrix N N ℝ) : Matrix N N ℝ := A * B - B * A

theorem commutator_conjugate (U : unitary (Matrix N N ℝ)) (A B : Matrix N N ℝ) :
    commutator (conjugate U A) (conjugate U B) = conjugate U (commutator A B) := by
  rw [commutator, commutator, map_sub, conjugate_mul, conjugate_mul]

theorem diagonal_commutator_apply (α : N → ℝ) (A : Matrix N N ℝ) (i j : N) :
    commutator (Matrix.diagonal α) A i j = (α i - α j) * A i j := by
  simp only [commutator, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

end Wikipedia.HomotopyGroupsOfSpheres.RealMatrixSquareNorm
