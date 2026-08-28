import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicRankOne

/-!
# Quaternionic unit columns and local frame completion in every rank

The matrix group and unit columns have their usual subspace topologies.
An explicit rank-one correction completes a column on the chart where
its distinguished coordinate is not `-1`.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicRankOne

local notation "ℍ" => Quaternion ℝ

variable (N : Type*) [Fintype N] [DecidableEq N]

abbrev SpGroup := unitary (Matrix N N ℍ)

abbrev UnitColumn := {v : N → ℍ // pairing v v = 1}

variable {N}

theorem pairing_axis (j : N) : pairing (axis j) (axis j) = 1 := by
  simp [pairing, axis, Pi.single_apply]

def axisColumn (j : N) : UnitColumn N := ⟨axis j, pairing_axis j⟩

/-- The usual column projection of a quaternionic unitary matrix. -/
def column (j : N) : C(SpGroup N, UnitColumn N) where
  toFun A := ⟨fun i => A.val i j, by
    have h := congrArg (fun B : Matrix N N ℍ => B j j) (Unitary.coe_star_mul_self A)
    simpa only [pairing, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] using h⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact continuous_subtype_val.matrix_elem i j

@[simp] theorem column_one (j : N) : column j 1 = axisColumn j := by
  apply Subtype.ext
  funext i
  simp [column, axisColumn, axis, Pi.single_apply, Matrix.one_apply]

theorem diagonal_mem_unitary (d : N → ℍ) (hd : ∀ i, d i ∈ unitary ℍ) :
    Matrix.diagonal d ∈ unitary (Matrix N N ℍ) := by
  constructor
  · change (Matrix.diagonal d)ᴴ * Matrix.diagonal d = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    exact (hd i).1
  · change Matrix.diagonal d * (Matrix.diagonal d)ᴴ = 1
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext i
    exact (hd i).2

/-- The diagonal involution negating only the distinguished axis. -/
def axisReflectionMatrix (j : N) : Matrix N N ℍ :=
  Matrix.diagonal (fun i => if i = j then -1 else 1)

theorem axisReflectionMatrix_unitary (j : N) :
    axisReflectionMatrix j ∈ unitary (Matrix N N ℍ) := by
  apply diagonal_mem_unitary
  intro i
  split_ifs <;> simp [Unitary.mem_iff]

theorem axisReflectionMatrix_sq (j : N) :
    axisReflectionMatrix j * axisReflectionMatrix j = 1 := by
  rw [axisReflectionMatrix, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  apply congrArg Matrix.diagonal
  funext i
  split_ifs <;> simp

def axisReflection (j : N) : SpGroup N :=
  ⟨axisReflectionMatrix j, axisReflectionMatrix_unitary j⟩

omit [Fintype N] in
theorem columnReflectionMatrix_column (v : N → ℍ) (j : N) (ha : v j ≠ -1) (i : N) :
    columnReflectionMatrix v j i j = -v i := by
  have hc : (1 + star (v j))⁻¹ * (star (v j) + 1) = 1 := by
    rw [add_comm (star (v j)), inv_mul_cancel₀ (one_add_star_ne_zero _ ha)]
  simp only [columnReflectionMatrix, Matrix.sub_apply, rankOne, Pi.add_apply,
    axis_self, star_add, star_one]
  rw [mul_assoc, hc, mul_one]
  by_cases hi : i = j
  · subst i
    simp [axis_self]
  · simp [hi, axis_of_ne i j hi]

omit [Fintype N] in
theorem columnReflectionMatrix_axis (j : N) :
    columnReflectionMatrix (axis j) j = axisReflectionMatrix j := by
  apply Matrix.ext
  intro i k
  by_cases hi : i = j <;> by_cases hk : k = j <;>
    simp_all [columnReflectionMatrix, rankOne, axis,
      axisReflectionMatrix, Matrix.one_apply, Matrix.diagonal_apply, apply_ite, eq_comm]

/-- A chart of the unit-column space containing the distinguished axis. -/
def columnChart (j : N) : Set (UnitColumn N) := {v | v.val j ≠ -1}

omit [DecidableEq N] in
theorem isOpen_columnChart (j : N) : IsOpen (columnChart j) :=
  isOpen_ne.preimage ((continuous_apply j).comp continuous_subtype_val)

theorem axisColumn_mem_chart (j : N) : axisColumn j ∈ columnChart j := by
  change axis j j ≠ -1
  rw [axis_self]
  intro h
  have hr := congrArg (fun q : ℍ => q.re) h
  change (1 : ℝ) = -1 at hr
  norm_num at hr

/-- An explicit quaternionic unitary completion of the column. -/
def sectionMap (j : N) (v : columnChart j) : SpGroup N :=
  ⟨columnReflectionMatrix v.val.val j,
    columnReflectionMatrix_unitary _ _ v.val.property v.property⟩ * axisReflection j

theorem column_sectionMap (j : N) (v : columnChart j) : column j (sectionMap j v) = v.val := by
  apply Subtype.ext
  funext i
  change (columnReflectionMatrix v.val.val j * axisReflectionMatrix j) i j = v.val.val i
  rw [axisReflectionMatrix, Matrix.mul_diagonal, if_pos rfl,
    columnReflectionMatrix_column _ _ v.property, mul_neg_one, neg_neg]

theorem sectionMap_axis (j : N) : sectionMap j ⟨axisColumn j, axisColumn_mem_chart j⟩ = 1 := by
  apply Subtype.ext
  change columnReflectionMatrix (axis j) j * axisReflectionMatrix j = 1
  rw [columnReflectionMatrix_axis, axisReflectionMatrix_sq]

theorem continuous_sectionMap (j : N) : Continuous (sectionMap j) := by
  have hv : Continuous (fun v : columnChart j => v.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hc : Continuous (fun v : columnChart j => (1 + star (v.val.val j))⁻¹) :=
    (continuous_const.add ((continuous_apply j).comp hv).star).inv₀
      (fun v => one_add_star_ne_zero _ v.property)
  have hR : Continuous (fun v : columnChart j => columnReflectionMatrix v.val.val j) := by
    apply continuous_matrix
    intro i k
    change Continuous (fun v : columnChart j => (1 : Matrix N N ℍ) i k -
      (v.val.val i + axis j i) * (1 + star (v.val.val j))⁻¹ * star (v.val.val k + axis j k))
    exact continuous_const.sub
      (((((continuous_apply i).comp hv).add continuous_const).mul hc).mul
        ((((continuous_apply k).comp hv).add continuous_const).star))
  exact (hR.subtype_mk _).mul continuous_const

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
