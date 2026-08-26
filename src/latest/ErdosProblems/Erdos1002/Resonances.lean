import ErdosProblems.Erdos1002.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Nearest-integer resonance coordinates

The manuscript fixes the smaller nearest integer at a half-integer tie.
The definition by a ceiling below encodes exactly that convention, rather
than relying on an implementation-dependent rounding operation.
-/

namespace Erdos1002

noncomputable section

/-- A nearest integer to `x`, with the smaller integer chosen at a tie. -/
def nearestInt (x : ℝ) : ℤ :=
  ⌈x - (1 : ℝ) / 2⌉

/-- The nearest numerator attached to denominator `p`. -/
def resonanceNumerator (p : ℕ) (α : ℝ) : ℤ :=
  nearestInt ((p : ℝ) * α)

/-- The signed displacement from the nearest integer cell. -/
def resonanceDelta (p : ℕ) (α : ℝ) : ℝ :=
  (p : ℝ) * α - resonanceNumerator p α

/-- The primitive-cell condition imposed on every shot in the manuscript. -/
def IsPrimitiveResonance (p : ℕ) (α : ℝ) : Prop :=
  Nat.Coprime (resonanceNumerator p α).natAbs p

instance (p : ℕ) (α : ℝ) : Decidable (IsPrimitiveResonance p α) :=
  by
    unfold IsPrimitiveResonance
    infer_instance

theorem measurable_nearestInt : Measurable nearestInt := by
  exact (measurable_id.sub_const ((1 : ℝ) / 2)).ceil

theorem measurable_resonanceNumerator (p : ℕ) :
    Measurable (resonanceNumerator p) := by
  exact measurable_nearestInt.comp (measurable_const.mul measurable_id)

theorem measurable_resonanceDelta (p : ℕ) :
    Measurable (resonanceDelta p) := by
  unfold resonanceDelta
  have hcast : Measurable (fun z : ℤ ↦ (z : ℝ)) :=
    measurable_of_countable _
  exact (measurable_const.mul measurable_id).sub
    (hcast.comp (measurable_resonanceNumerator p))

theorem measurableSet_isPrimitiveResonance (p : ℕ) :
    MeasurableSet {α : ℝ | IsPrimitiveResonance p α} := by
  change MeasurableSet
    (resonanceNumerator p ⁻¹' {q : ℤ | Nat.Coprime q.natAbs p})
  exact (measurable_resonanceNumerator p)
    ((Set.to_countable {q : ℤ | Nat.Coprime q.natAbs p}).measurableSet)

theorem nearestInt_add_int (x : ℝ) (z : ℤ) :
    nearestInt (x + z) = nearestInt x + z := by
  unfold nearestInt
  have h : x + (z : ℝ) - (1 : ℝ) / 2 =
      (x - (1 : ℝ) / 2) + (z : ℝ) := by ring
  rw [h, Int.ceil_add_intCast]

theorem resonanceNumerator_add_int (p : ℕ) (α : ℝ) (z : ℤ) :
    resonanceNumerator p (α + z) =
      resonanceNumerator p α + (p : ℤ) * z := by
  unfold resonanceNumerator
  have h : (p : ℝ) * (α + (z : ℝ)) =
      (p : ℝ) * α + (((p : ℤ) * z : ℤ) : ℝ) := by
    push_cast
    ring
  rw [h, nearestInt_add_int]

theorem resonanceDelta_add_int (p : ℕ) (α : ℝ) (z : ℤ) :
    resonanceDelta p (α + z) = resonanceDelta p α := by
  rw [resonanceDelta, resonanceDelta, resonanceNumerator_add_int]
  push_cast
  ring

theorem resonanceDelta_periodic (p : ℕ) :
    Function.Periodic (resonanceDelta p) 1 := by
  intro α
  simpa using! resonanceDelta_add_int p α (1 : ℤ)

theorem resonanceNumerator_bounds_of_mem_unitInterval
    (p : ℕ) {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) :
    0 ≤ resonanceNumerator p α ∧ resonanceNumerator p α ≤ (p : ℤ) := by
  unfold resonanceNumerator nearestInt
  constructor
  · apply Int.ceil_nonneg_of_neg_one_lt
    have hp : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have : 0 ≤ (p : ℝ) * α := mul_nonneg hp hα.1.le
    linarith
  · rw [Int.ceil_le]
    have hp : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have : (p : ℝ) * α ≤ (p : ℝ) := by
      nlinarith [hα.2]
    exact_mod_cast (show (p : ℝ) * α - (1 : ℝ) / 2 ≤ (p : ℝ) by linarith)

theorem nearestInt_spec (x : ℝ) :
    -(1 : ℝ) / 2 < x - nearestInt x ∧ x - nearestInt x ≤ (1 : ℝ) / 2 := by
  constructor
  · have h := Int.ceil_lt_add_one (x - (1 : ℝ) / 2)
    change ((nearestInt x : ℤ) : ℝ) < x - (1 : ℝ) / 2 + 1 at h
    linarith
  · have h := Int.le_ceil (x - (1 : ℝ) / 2)
    change x - (1 : ℝ) / 2 ≤ ((nearestInt x : ℤ) : ℝ) at h
    linarith

theorem resonanceDelta_mem (p : ℕ) (α : ℝ) :
    resonanceDelta p α ∈ Set.Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2) := by
  exact nearestInt_spec ((p : ℝ) * α)

/-- The half-open nearest-cell condition characterizes the chosen integer. -/
theorem nearestInt_eq_of_mem {x : ℝ} {q : ℤ}
    (hq : x - (q : ℝ) ∈ Set.Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) :
    nearestInt x = q := by
  unfold nearestInt
  rw [Int.ceil_eq_iff]
  constructor <;> linarith [hq.1, hq.2]

theorem resonanceNumerator_eq_of_delta_mem {p : ℕ} {α : ℝ} {q : ℤ}
    (hq : (p : ℝ) * α - (q : ℝ) ∈
      Set.Ioc (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) :
    resonanceNumerator p α = q := by
  exact nearestInt_eq_of_mem hq

theorem resonanceNumerator_eq_of_abs_sub_lt_half
    {p : ℕ} {α : ℝ} {q : ℤ}
    (hq : |(p : ℝ) * α - (q : ℝ)| < (1 : ℝ) / 2) :
    resonanceNumerator p α = q := by
  apply resonanceNumerator_eq_of_delta_mem
  rw [Set.mem_Ioc]
  constructor
  · linarith [(abs_lt.mp hq).1]
  · exact (abs_lt.mp hq).2.le

theorem resonanceDelta_eq_of_abs_sub_lt_half
    {p : ℕ} {α : ℝ} {q : ℤ}
    (hq : |(p : ℝ) * α - (q : ℝ)| < (1 : ℝ) / 2) :
    resonanceDelta p α = (p : ℝ) * α - (q : ℝ) := by
  rw [resonanceDelta, resonanceNumerator_eq_of_abs_sub_lt_half hq]

/-- Open nearest-integer cells are disjoint. -/
theorem eq_of_two_nearest_cell_bounds
    {p : ℕ} {α : ℝ} {q q' : ℤ}
    (hq : |(p : ℝ) * α - (q : ℝ)| < (1 : ℝ) / 2)
    (hq' : |(p : ℝ) * α - (q' : ℝ)| < (1 : ℝ) / 2) :
    q = q' := by
  rw [← resonanceNumerator_eq_of_abs_sub_lt_half hq,
    resonanceNumerator_eq_of_abs_sub_lt_half hq']

theorem resonanceDelta_eq_zero_iff (p : ℕ) (α : ℝ) :
    resonanceDelta p α = 0 ↔ (p : ℝ) * α = resonanceNumerator p α := by
  change (p : ℝ) * α - (resonanceNumerator p α : ℝ) = 0 ↔
    (p : ℝ) * α = (resonanceNumerator p α : ℝ)
  exact sub_eq_zero

end

end Erdos1002
