import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Fin.Tuple.Basic

/-! # A scalar diagonal block and its exact finite-matrix identities -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.MatrixBorder

variable {R : Type*} [Semiring R] {n : ℕ}

def border (a : R) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of (Fin.cons (Fin.cons a (fun _ ↦ 0)) (fun i ↦ Fin.cons 0 (fun j ↦ A i j)))

@[simp] theorem border_zero_zero (a : R) (A : Matrix (Fin n) (Fin n) R) :
    border a A 0 0 = a := rfl

@[simp] theorem border_zero_succ (a : R) (A : Matrix (Fin n) (Fin n) R) (j : Fin n) :
    border a A 0 j.succ = 0 := rfl

@[simp] theorem border_succ_zero (a : R) (A : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    border a A i.succ 0 = 0 := rfl

@[simp] theorem border_succ_succ (a : R) (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    border a A i.succ j.succ = A i j := rfl

theorem border_one : border (1 : R) (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [border, Matrix.one_apply, eq_comm]

theorem border_mul (a b : R) (A B : Matrix (Fin n) (Fin n) R) :
    border (a * b) (A * B) = border a A * border b B := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [border, Matrix.mul_apply, Fin.sum_univ_succ]

theorem transpose_border (a : R) (A : Matrix (Fin n) (Fin n) R) :
    (border a A).transpose = border a A.transpose := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> rfl

theorem star_border [StarRing R] (a : R) (A : Matrix (Fin n) (Fin n) R) :
    star (border a A) = border (star a) (star A) := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [border, Matrix.star_apply]

theorem border_unitary [StarRing R] (a : unitary R)
    (A : unitary (Matrix (Fin n) (Fin n) R)) :
    border a.val A.val ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) R) := by
  constructor
  · rw [star_border, ← border_mul, Unitary.coe_star_mul_self, Unitary.coe_star_mul_self,
      border_one]
  · rw [star_border, ← border_mul, a.property.2, A.property.2, border_one]

def unitaryBorder [StarRing R] :
    unitary R × unitary (Matrix (Fin n) (Fin n) R) →*
      unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) R) where
  toFun p := ⟨border p.1.val p.2.val, border_unitary p.1 p.2⟩
  map_one' := Subtype.ext border_one
  map_mul' p q := Subtype.ext (border_mul p.1.val q.1.val p.2.val q.2.val)

theorem continuous_border [TopologicalSpace R] (a : R) :
    Continuous (fun A : Matrix (Fin n) (Fin n) R ↦ border a A) := by
  apply continuous_matrix
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    first | exact continuous_const | exact continuous_apply_apply _ _

theorem det_border {K : Type*} [CommRing K] (a : K) (A : Matrix (Fin n) (Fin n) K) :
    (border a A).det = a * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [border_zero_zero, Fin.val_zero, pow_zero, one_mul,
    border_zero_succ, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1

end Wikipedia.HomotopyGroupsOfSpheres.MatrixBorder
