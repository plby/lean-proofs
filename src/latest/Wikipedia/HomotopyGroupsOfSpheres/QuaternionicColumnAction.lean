import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

/-! # The natural quaternionic matrix action on unit columns in every rank -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicRankOne

local notation "ℍ" => Quaternion ℝ

variable {N : Type*} [Fintype N] [DecidableEq N]

def negColumn (v : UnitColumn N) : UnitColumn N :=
  ⟨-v.val, by simpa only [pairing, Pi.neg_apply, star_neg, neg_mul_neg] using v.property⟩

theorem column_neg (j : N) (A : SpGroup N) : column j (-A) = negColumn (column j A) := rfl

/-- Every quaternionic unit column extends to a unitary frame. -/
theorem column_surjective (j : N) : Function.Surjective (column j) := by
  intro v
  by_cases hv : v.val j ≠ -1
  · exact ⟨sectionMap j ⟨v, hv⟩, column_sectionMap j ⟨v, hv⟩⟩
  · have hneg : (negColumn v).val j ≠ -1 := by
      change -v.val j ≠ -1
      rw [not_not.mp hv, neg_neg]
      simpa only [columnChart, Set.mem_ofPred_eq, axisColumn, axis_self] using
        axisColumn_mem_chart j
    refine ⟨-sectionMap j ⟨negColumn v, hneg⟩, ?_⟩
    rw [column_neg, column_sectionMap]
    apply Subtype.ext
    exact neg_neg v.val

def vectorAction (A : SpGroup N) (v : N → ℍ) : N → ℍ := A.val *ᵥ v

theorem vectorAction_column (j : N) (A B : SpGroup N) :
    vectorAction A (column j B).val = (column j (A * B)).val := by
  funext i
  simp only [vectorAction, Matrix.mulVec, dotProduct, column, ContinuousMap.coe_mk,
    Submonoid.coe_mul, Matrix.mul_apply]

theorem vectorAction_mem (j : N) (A : SpGroup N) (v : UnitColumn N) :
    pairing (vectorAction A v.val) (vectorAction A v.val) = 1 := by
  obtain ⟨B, rfl⟩ := column_surjective j v
  rw [vectorAction_column]
  exact (column j (A * B)).property

/-- The ordinary matrix action, restricted to the unit-column sphere. -/
def action (j : N) (A : SpGroup N) (v : UnitColumn N) : UnitColumn N :=
  ⟨vectorAction A v.val, vectorAction_mem j A v⟩

@[simp] theorem action_column (j : N) (A B : SpGroup N) :
    action j A (column j B) = column j (A * B) :=
  Subtype.ext (vectorAction_column j A B)

@[simp] theorem action_axis (j : N) (A : SpGroup N) :
    action j A (axisColumn j) = column j A := by
  rw [← column_one j, action_column, mul_one]

@[simp] theorem action_one (j : N) (v : UnitColumn N) : action j 1 v = v := by
  obtain ⟨B, rfl⟩ := column_surjective j v
  rw [action_column, one_mul]

theorem action_mul (j : N) (A B : SpGroup N) (v : UnitColumn N) :
    action j (A * B) v = action j A (action j B v) := by
  obtain ⟨C, rfl⟩ := column_surjective j v
  simp only [action_column, mul_assoc]

@[simp] theorem action_inv_cancel (j : N) (A : SpGroup N) (v : UnitColumn N) :
    action j A (action j A⁻¹ v) = v := by
  rw [← action_mul, mul_inv_cancel, action_one]

@[simp] theorem action_inv_column (j : N) (A : SpGroup N) :
    action j A⁻¹ (column j A) = axisColumn j := by
  rw [action_column, inv_mul_cancel, column_one]

theorem continuous_vectorAction :
    Continuous (fun z : SpGroup N × (N → ℍ) => vectorAction z.1 z.2) := by
  apply continuous_pi
  intro i
  change Continuous (fun z : SpGroup N × (N → ℍ) => ∑ k, z.1.val i k * z.2 k)
  apply continuous_finsetSum
  intro k _
  exact ((continuous_subtype_val.comp continuous_fst).matrix_elem i k).mul
    ((continuous_apply k).comp continuous_snd)

theorem continuous_action (j : N) :
    Continuous (fun z : SpGroup N × UnitColumn N => action j z.1 z.2) := by
  have h : Continuous (fun z : SpGroup N × UnitColumn N => (z.1, z.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  apply Continuous.subtype_mk
  change Continuous (fun z : SpGroup N × UnitColumn N => vectorAction z.1 z.2.val)
  exact (continuous_vectorAction (N := N)).comp h

omit [DecidableEq N] in
theorem continuous_pairing :
    Continuous (fun z : UnitColumn N × UnitColumn N => pairing z.1.val z.2.val) := by
  apply continuous_finsetSum
  intro i _
  exact (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).star).mul
    ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))

theorem action_inv_coordinate (j : N) (A : SpGroup N) (v : UnitColumn N) :
    (action j A⁻¹ v).val j = pairing (column j A).val v.val := rfl

theorem column_inv_mul_eq_axis_iff (j : N) (A B : SpGroup N) :
    column j (A⁻¹ * B) = axisColumn j ↔ column j A = column j B := by
  rw [← action_column]
  constructor
  · intro h
    have hh := congrArg (action j A) h
    simpa only [action_inv_cancel, action_axis] using hh.symm
  · intro h
    rw [← h, action_inv_column]

/-- The actual stabilizer of the chosen unit column. -/
def axisSubgroup (j : N) : Subgroup (SpGroup N) where
  carrier := {A | column j A = axisColumn j}
  one_mem' := column_one j
  mul_mem' {A B} hA hB := by
    rw [Set.mem_ofPred_eq, ← action_column, hB, action_axis, hA]
  inv_mem' {A} hA := by
    have h := action_inv_column j A
    rw [hA, action_axis] at h
    exact h

theorem isClosed_axisSubgroup (j : N) : IsClosed (axisSubgroup j : Set (SpGroup N)) :=
  isClosed_singleton.preimage (column j).continuous

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
