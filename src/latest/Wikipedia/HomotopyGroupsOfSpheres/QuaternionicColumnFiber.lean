import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

/-! # The first-column fiber in quaternionic rank `n+1` is the actual rank-`n` group -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicRankOne

local notation "ℍ" => Quaternion ℝ

variable {n : ℕ}

/-- Border a quaternionic matrix by a first diagonal entry equal to one. -/
def bordered (A : Matrix (Fin n) (Fin n) ℍ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ :=
  Matrix.of (Fin.cons (Fin.cons 1 (fun _ => 0)) (fun i => Fin.cons 0 (fun j => A i j)))

theorem bordered_one : bordered (1 : Matrix (Fin n) (Fin n) ℍ) = 1 := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [bordered, Matrix.one_apply, eq_comm]

theorem bordered_mul (A B : Matrix (Fin n) (Fin n) ℍ) :
    bordered (A * B) = bordered A * bordered B := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [bordered, Matrix.mul_apply, Fin.sum_univ_succ]

theorem star_bordered (A : Matrix (Fin n) (Fin n) ℍ) :
    star (bordered A) = bordered (star A) := by
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [bordered, Matrix.star_apply]

theorem bordered_unitary (A : SpGroup (Fin n)) :
    bordered A.val ∈ unitary (Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) := by
  constructor
  · rw [star_bordered, ← bordered_mul, Unitary.star_mul_self_of_mem A.property, bordered_one]
  · rw [star_bordered, ← bordered_mul, Unitary.mul_star_self_of_mem A.property, bordered_one]

/-- The standard quaternionic rank-stabilization homomorphism. -/
def stabilization (n : ℕ) : SpGroup (Fin n) →* SpGroup (Fin (n + 1)) where
  toFun A := ⟨bordered A.val, bordered_unitary A⟩
  map_one' := Subtype.ext bordered_one
  map_mul' A B := Subtype.ext (bordered_mul A.val B.val)

theorem continuous_stabilization (n : ℕ) : Continuous (stabilization n) := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    dsimp [stabilization, bordered] <;>
    simp only [Fin.cons_zero, Fin.cons_succ] <;>
    first | exact continuous_const | exact continuous_subtype_val.matrix_elem _ _

@[simp] theorem column_stabilization (A : SpGroup (Fin n)) :
    column 0 (stabilization n A) = axisColumn 0 := by
  apply Subtype.ext
  funext i
  cases i using Fin.cases <;> simp [column, stabilization, bordered, axisColumn, axis]

theorem fiber_entry_zero_zero (A : SpGroup (Fin (n + 1)))
    (h : column 0 A = axisColumn 0) : A.val 0 0 = 1 := by
  have hh := congrArg (fun v : UnitColumn (Fin (n + 1)) => v.val 0) h
  simpa [column, axisColumn, axis] using hh

theorem fiber_entry_succ_zero (A : SpGroup (Fin (n + 1)))
    (h : column 0 A = axisColumn 0) (i : Fin n) : A.val i.succ 0 = 0 := by
  have hh := congrArg (fun v : UnitColumn (Fin (n + 1)) => v.val i.succ) h
  simpa [column, axisColumn, axis] using hh

theorem fiber_entry_zero_succ (A : SpGroup (Fin (n + 1)))
    (h : column 0 A = axisColumn 0) (i : Fin n) : A.val 0 i.succ = 0 := by
  have hh := congrArg (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ => B 0 i.succ)
    (Unitary.coe_star_mul_self A)
  simpa [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_succ,
    fiber_entry_zero_zero A h, fiber_entry_succ_zero A h, Matrix.one_apply, eq_comm] using hh

/-- Restrict a bordered matrix to its lower-right block. -/
def lowerBlock (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) : Matrix (Fin n) (Fin n) ℍ :=
  fun i j => A i.succ j.succ

theorem lowerBlock_unitary (A : SpGroup (Fin (n + 1))) (h : column 0 A = axisColumn 0) :
    lowerBlock A.val ∈ unitary (Matrix (Fin n) (Fin n) ℍ) := by
  constructor
  · apply Matrix.ext
    intro i j
    have hh := congrArg (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ => B i.succ j.succ)
      (Unitary.coe_star_mul_self A)
    simpa [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_succ, lowerBlock,
      fiber_entry_zero_succ A h, Matrix.one_apply] using hh
  · apply Matrix.ext
    intro i j
    have hh := congrArg (fun B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ => B i.succ j.succ)
      (Unitary.coe_mul_star_self A)
    simpa [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_succ, lowerBlock,
      fiber_entry_succ_zero A h, Matrix.one_apply] using hh

abbrev AxisFiber (n : ℕ) :=
  {A : SpGroup (Fin (n + 1)) // column 0 A = axisColumn 0}

def lower (A : AxisFiber n) : SpGroup (Fin n) :=
  ⟨lowerBlock A.val.val, lowerBlock_unitary A.val A.property⟩

theorem stabilization_lower (A : AxisFiber n) : stabilization n (lower A) = A.val := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [stabilization, bordered, lower, lowerBlock, fiber_entry_zero_zero A.val A.property,
      fiber_entry_succ_zero A.val A.property, fiber_entry_zero_succ A.val A.property]

theorem continuous_lower : Continuous (lower (n := n)) := by
  apply Continuous.subtype_mk
  apply continuous_matrix
  intro i j
  exact (continuous_subtype_val.comp continuous_subtype_val).matrix_elem i.succ j.succ

/-- The fiber identification retains the original matrix entries and subspace topologies. -/
def fiberHomeomorph (n : ℕ) : SpGroup (Fin n) ≃ₜ AxisFiber n where
  toFun A := ⟨stabilization n A, column_stabilization A⟩
  invFun := lower
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := Subtype.ext (stabilization_lower A)
  continuous_toFun := (continuous_stabilization n).subtype_mk _
  continuous_invFun := continuous_lower

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
