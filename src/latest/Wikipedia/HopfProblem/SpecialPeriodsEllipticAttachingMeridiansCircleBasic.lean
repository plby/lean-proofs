import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupMeridians
import Mathlib.Tactic.FunProp

/-!
# Actual clockwise circles in the twice-punctured plane

A nonzero coefficient of norm less than one gives a genuine loop around
either deleted point. At the fixed coefficients `1/2` and `-1/2`, these
clockwise loops agree pointwise with the inverses of the original positive
meridians based at `1/2`.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians

open Triangle

/-- The actual finite puncture indexed by the fixed meridian basis. -/
def center (b : Bool) : ℂ := if b then 1 else 0

/-- One clockwise turn of the unit circle. -/
def clockwiseUnit (t : unitInterval) : ℂ :=
  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (t : ℝ))

theorem clockwiseUnit_continuous : Continuous clockwiseUnit := by
  unfold clockwiseUnit
  fun_prop

theorem clockwiseUnit_ne_zero (t : unitInterval) : clockwiseUnit t ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] theorem norm_clockwiseUnit (t : unitInterval) : ‖clockwiseUnit t‖ = 1 := by
  simp [clockwiseUnit, Complex.norm_exp]

@[simp] theorem clockwiseUnit_zero : clockwiseUnit 0 = 1 := by
  simp [clockwiseUnit]

@[simp] theorem clockwiseUnit_one : clockwiseUnit 1 = 1 := by
  change Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * (1 : ℝ)) = 1
  rw [Complex.ofReal_one, mul_one, neg_mul]
  simpa only [zero_sub, Complex.exp_zero] using Complex.exp_periodic.sub_eq (0 : ℂ)

/-- The literal complex-coordinate formula used by the attaching circles. -/
def clockwiseCircle (b : Bool) (A : ℂ) (t : unitInterval) : ℂ :=
  center b + A * clockwiseUnit t

theorem clockwiseCircle_continuous (b : Bool) (A : ℂ) :
    Continuous (clockwiseCircle b A) :=
  continuous_const.add (continuous_const.mul clockwiseUnit_continuous)

@[simp] theorem clockwiseCircle_zero (b : Bool) (A : ℂ) :
    clockwiseCircle b A 0 = center b + A := by simp [clockwiseCircle]

@[simp] theorem clockwiseCircle_one (b : Bool) (A : ℂ) :
    clockwiseCircle b A 1 = center b + A := by simp [clockwiseCircle]

/-- A punctured open unit disk about either center avoids both deleted
points of the actual twice-punctured plane. -/
theorem center_add_mem_twicePuncturedPlaneDomain (b : Bool) {z : ℂ}
    (hz : z ≠ 0) (hn : ‖z‖ < 1) : center b + z ∈ twicePuncturedPlaneDomain := by
  have hz₁ : z ≠ 1 := by
    intro h
    rw [h, norm_one] at hn
    exact (lt_irrefl 1) hn
  have hzneg : z ≠ -1 := by
    intro h
    rw [h, norm_neg, norm_one] at hn
    exact (lt_irrefl 1) hn
  change center b + z ≠ 0 ∧ center b + z ≠ 1
  cases b with
  | false => simpa only [center, Bool.false_eq_true, ↓reduceIte, zero_add] using And.intro hz hz₁
  | true =>
    change 1 + z ≠ 0 ∧ 1 + z ≠ 1
    constructor
    · intro h
      apply hzneg
      calc
        z = (1 + z) - 1 := by ring
        _ = -1 := by rw [h, zero_sub]
    · intro h
      exact hz (add_left_cancel (h.trans (add_zero 1).symm))

theorem clockwiseCircle_mem (b : Bool) (A : ℂ) (hA : A ≠ 0) (hAn : ‖A‖ < 1)
    (t : unitInterval) : clockwiseCircle b A t ∈ twicePuncturedPlaneDomain := by
  apply center_add_mem_twicePuncturedPlaneDomain b
  · exact mul_ne_zero hA (clockwiseUnit_ne_zero t)
  · simpa only [norm_mul, norm_clockwiseUnit, mul_one] using hAn

/-- The actual moving basepoint of a clockwise circle. -/
def circleBasepoint (b : Bool) (A : ℂ) (hA : A ≠ 0) (hAn : ‖A‖ < 1) :
    TwicePuncturedPlane :=
  ⟨center b + A, center_add_mem_twicePuncturedPlaneDomain b hA hAn⟩

@[simp] theorem circleBasepoint_coe (b : Bool) (A : ℂ) (hA : A ≠ 0) (hAn : ‖A‖ < 1) :
    (circleBasepoint b A hA hAn : ℂ) = center b + A := rfl

/-- The actual clockwise path in the literal punctured-plane subtype. -/
def clockwiseCirclePath (b : Bool) (A : ℂ) (hA : A ≠ 0) (hAn : ‖A‖ < 1) :
    Path (circleBasepoint b A hA hAn) (circleBasepoint b A hA hAn) where
  toFun t := ⟨clockwiseCircle b A t, clockwiseCircle_mem b A hA hAn t⟩
  continuous_toFun := (clockwiseCircle_continuous b A).subtype_mk _
  source' := Subtype.ext (clockwiseCircle_zero b A)
  target' := Subtype.ext (clockwiseCircle_one b A)

@[simp] theorem clockwiseCirclePath_coe (b : Bool) (A : ℂ)
    (hA : A ≠ 0) (hAn : ‖A‖ < 1) (t : unitInterval) :
    (clockwiseCirclePath b A hA hAn t : ℂ) = clockwiseCircle b A t := rfl

/-- The coefficient of the original meridian based at `1/2`. -/
def anchor (b : Bool) : ℂ := if b then -(1 / 2) else 1 / 2

theorem anchor_ne_zero (b : Bool) : anchor b ≠ 0 := by
  cases b <;> norm_num [anchor]

theorem norm_anchor_lt_one (b : Bool) : ‖anchor b‖ < 1 := by
  cases b <;> norm_num [anchor, norm_div]

@[simp] theorem center_add_anchor (b : Bool) : center b + anchor b = 1 / 2 := by
  cases b <;> norm_num [center, anchor]

/-- The inverse of the exact original positive meridian, not a new
choice of an abstract generator. -/
def fixedClockwiseMeridian (b : Bool) : Path meridianBasepoint meridianBasepoint :=
  (if b then positiveMeridianOne else positiveMeridianZero).symm

private theorem positiveTurn_symm (t : unitInterval) :
    Complex.exp ((2 * Real.pi : ℂ) * Complex.I * (unitInterval.symm t : ℝ)) =
      clockwiseUnit t := by
  rw [unitInterval.coe_symm_eq]
  have he : (2 * Real.pi : ℂ) * Complex.I * ((1 - (t : ℝ) : ℝ) : ℂ) =
      -(2 * Real.pi : ℂ) * Complex.I * (t : ℝ) + 2 * Real.pi * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_periodic]
  rfl

/-- The orientation comparison is an exact equality of the original
path's complex coordinates, throughout the full unit interval. -/
theorem fixedClockwiseMeridian_coe (b : Bool) (t : unitInterval) :
    (fixedClockwiseMeridian b t : ℂ) = clockwiseCircle b (anchor b) t := by
  cases b with
  | false =>
    change (positiveMeridianZero (unitInterval.symm t) : ℂ) = _
    rw [positiveMeridianZero_apply, positiveTurn_symm]
    simp [clockwiseCircle, center, anchor]
  | true =>
    change (positiveMeridianOne (unitInterval.symm t) : ℂ) = _
    rw [positiveMeridianOne_apply, positiveTurn_symm]
    simp [clockwiseCircle, center, anchor, sub_eq_add_neg]

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingMeridians
