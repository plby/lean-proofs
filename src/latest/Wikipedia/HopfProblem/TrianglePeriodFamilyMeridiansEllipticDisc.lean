import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansCircle
import Wikipedia.HopfProblem.EllipticFamilies
import Mathlib.Topology.UnitInterval

/-!
# Elliptic meridians in the actual unit disc

At a positive radius smaller than one, the path with phase `t / j.order`
remains nonzero and ends at the inverse elliptic rotation of its initial
point.  Raising its disc coordinate to the elliptic order traces one
positive turn.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

/-- A positive real base point in the actual open unit disc. -/
def ellipticDiscBase (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : SpecialPeriods.Disc :=
  ⟨(r : ℂ), by
    simpa [SpecialPeriods.unitDisc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      using hr1⟩

@[simp] theorem ellipticDiscBase_val (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (ellipticDiscBase r hr hr1 : ℂ) = (r : ℂ) := rfl

theorem ellipticDiscBase_ne_zero (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (ellipticDiscBase r hr hr1 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr hr.ne'

/-- The nonzero disc path lifting one positive turn through an elliptic power map. -/
def ellipticDiscTurn (j : Elliptic.Kind) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (t : unitInterval) : SpecialPeriods.Disc :=
  ⟨(r : ℂ) * turn ((t : ℝ) / j.order), by
    simpa [SpecialPeriods.unitDisc, norm_mul, norm_turn, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr] using hr1⟩

@[simp] theorem ellipticDiscTurn_val (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    (ellipticDiscTurn j r hr hr1 t : ℂ) = (r : ℂ) * turn ((t : ℝ) / j.order) := rfl

theorem ellipticDiscTurn_continuous (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) : Continuous (ellipticDiscTurn j r hr hr1) :=
  (continuous_const.mul
    (continuous_turn.comp (continuous_subtype_val.div_const (j.order : ℝ)))).subtype_mk _

theorem ellipticDiscTurn_ne_zero (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    (ellipticDiscTurn j r hr hr1 t : ℂ) ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (turn_ne_zero _)

@[simp] theorem ellipticDiscTurn_zero (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    ellipticDiscTurn j r hr hr1 0 = ellipticDiscBase r hr hr1 := by
  apply Subtype.ext
  simp [ellipticDiscTurn, ellipticDiscBase]

@[simp] theorem ellipticDiscTurn_one (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    ellipticDiscTurn j r hr hr1 1 =
      (Elliptic.familyRotation j).symm (ellipticDiscBase r hr hr1) := by
  apply (Elliptic.familyRotation j).injective
  change (Elliptic.familyRotation j) (ellipticDiscTurn j r hr hr1 1) =
    (Elliptic.familyRotation j) ((Elliptic.familyRotation j).symm (ellipticDiscBase r hr hr1))
  rw [(Elliptic.familyRotation j).apply_symm_apply]
  cases j
  · apply Subtype.ext
    change -SpecialPeriods.rho * ((r : ℂ) * turn (1 / 3)) = (r : ℂ)
    have hρ : -SpecialPeriods.rho ≠ 0 := by
      intro h
      have hn := congrArg norm h
      simp [SpecialPeriods.norm_rho] at hn
    rw [turn_one_third, mul_left_comm, mul_inv_cancel₀ hρ, mul_one]
  · apply Subtype.ext
    change -Complex.I * ((r : ℂ) * turn (1 / 4)) = (r : ℂ)
    rw [turn_one_quarter, mul_left_comm]
    simp

/-- The quotient power coordinate makes exactly one positive turn. -/
theorem ellipticDiscTurn_pow (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    (ellipticDiscTurn j r hr hr1 t : ℂ) ^ j.order =
      (r : ℂ) ^ j.order * turn (t : ℝ) := by
  rw [ellipticDiscTurn_val, mul_pow, turn_div_nat_pow (t : ℝ) j.order j.order_pos]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
