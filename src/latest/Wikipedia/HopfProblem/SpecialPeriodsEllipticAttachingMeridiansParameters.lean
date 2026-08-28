import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansChart
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansLinearization
import Wikipedia.HopfProblem.SpecialPeriodsEllipticAttachingMeridiansCircleBasic
import Wikipedia.HopfProblem.EllipticLogGaugeFundamentalGroup

/-!
# Actual small logarithmic parameters for the elliptic meridians

The original normalized elliptic coordinate supplies the analytic
linearization estimates. Intersecting their positive radius with the
selected filling radius gives actual logarithmic attaching parameters
without any additional existence hypothesis. The powered logarithmic
coordinate makes exactly one clockwise turn.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry

open Elliptic Elliptic.LogGauge EllipticAttachingMeridians CuspUniformization

/-- The two actual elliptic points use the original finite-meridian labels. -/
def attachingMeridianIndex : Kind → Bool
  | .three => false
  | .four => true

@[simp] theorem attachingMeridianIndex_three : attachingMeridianIndex .three = false := rfl

@[simp] theorem attachingMeridianIndex_four : attachingMeridianIndex .four = true := rfl

/-- The original plane-coordinate normalizations agree with the fixed
twice-punctured-plane meridian centers. -/
theorem attachingPlaneCoordinate_zero_eq_center (j : Kind) :
    attachingPlaneCoordinate j 0 =
      EllipticAttachingMeridians.center (attachingMeridianIndex j) := by
  cases j with
  | three => exact attachingPlaneCoordinate_three_zero
  | four => exact attachingPlaneCoordinate_four_zero

/-- The actual local analytic control, constructed from the proved
analyticity and nonzero derivative of the original coordinate. -/
def attachingPlaneControl (j : Kind) : LinearizationControl (attachingPlaneCoordinate j) :=
  analyticLinearizationControl (attachingPlaneCoordinate_analyticAt_zero j)
    (attachingPlaneCoordinate_deriv_zero_ne_zero j)

/-- A radius valid both for the original filling and for its actual
analytic straight-line comparison with the derivative. -/
def attachingMeridianRadius (j : Kind) : ℝ :=
  min (specialBaseCover.radius (some j)) (attachingPlaneControl j).radius

theorem attachingMeridianRadius_pos (j : Kind) : 0 < attachingMeridianRadius j :=
  lt_min (specialBaseCover.radius_pos (some j)) (attachingPlaneControl j).radius_pos

theorem attachingMeridianRadius_le_filling (j : Kind) :
    attachingMeridianRadius j ≤ specialBaseCover.radius (some j) := min_le_left _ _

theorem attachingMeridianRadius_le_control (j : Kind) :
    attachingMeridianRadius j ≤ (attachingPlaneControl j).radius := min_le_right _ _

/-- Logarithmic attaching parameters satisfying both actual radius
requirements exist for each of the two elliptic fillings. -/
theorem exists_small_attaching_parameters (j : Kind) :
    ∃ s₀ : ℂ, 0 < s₀.im ∧ ‖exponential s₀‖ ^ j.order < attachingMeridianRadius j :=
  exists_logMeridian_parameters j (attachingMeridianRadius j) (attachingMeridianRadius_pos j)

theorem attaching_parameters_filling_bound (j : Kind) {s₀ : ℂ}
    (hr : ‖exponential s₀‖ ^ j.order < attachingMeridianRadius j) :
    ‖exponential s₀‖ ^ j.order < specialBaseCover.radius (some j) :=
  hr.trans_le (attachingMeridianRadius_le_filling j)

theorem attaching_parameters_control_bound (j : Kind) {s₀ : ℂ}
    (hr : ‖exponential s₀‖ ^ j.order < attachingMeridianRadius j) :
    ‖exponential s₀ ^ j.order‖ < (attachingPlaneControl j).radius := by
  rw [norm_pow]
  exact hr.trans_le (attachingMeridianRadius_le_control j)

theorem attaching_initial_coordinate_ne_zero (j : Kind) (s₀ : ℂ) :
    exponential s₀ ^ j.order ≠ 0 :=
  pow_ne_zero j.order (exponential_ne_zero s₀)

/-- The exact powered logarithmic coordinate makes one clockwise turn,
throughout the entire interval, for either elliptic order. -/
theorem attaching_log_parameter_clockwise (j : Kind) (s₀ : ℂ) (t : I) :
    exponential (s₀ - ((t : ℝ) : ℂ) / (j.order : ℂ)) ^ j.order =
      exponential s₀ ^ j.order * clockwiseUnit t := by
  have hn : (j.order : ℂ) ≠ 0 := by exact_mod_cast j.order_pos.ne'
  simp only [exponential, clockwiseUnit, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  field_simp
  ring

/-- The genuine disc-valued root path has the same exact clockwise
power-coordinate formula. -/
theorem attaching_log_root_clockwise (j : Kind) (s₀ : ℂ) (hs₀ : 0 < s₀.im) (t : I) :
    (logMeridianRoot j s₀ hs₀ t : ℂ) ^ j.order =
      exponential s₀ ^ j.order * clockwiseUnit t :=
  attaching_log_parameter_clockwise j s₀ t

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.EllipticGeometry
