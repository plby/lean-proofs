import ErdosProblems.Erdos1038.TaoUpperTwoAtomTrial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The interval-density trials in Tao's sharp upper argument

The second and third parameter ranges in Tao's proof use constant densities
on intervals ending at `2 * sqrt 2`.  This file makes the analytic reduction
to Tao's primitive

`F(x) = x - x * log |x|`

exact, including when an endpoint of the translated interval is zero.  It
then records the exact rational parameters and scalar potentials from
equations (2.5) and (2.6) of the updated note.
-/

open Set
open scoped Interval

namespace Erdos1038

noncomputable section

/-- Tao's antiderivative of `x ↦ log (1 / |x|)`.  Mathlib's convention
`Real.log 0 = 0` makes this definition continuous at zero. -/
def taoLogPrimitive (x : ℝ) : ℝ :=
  x - x * Real.log |x|

theorem taoLogPrimitive_zero : taoLogPrimitive 0 = 0 := by
  simp [taoLogPrimitive]

theorem continuous_taoLogPrimitive : Continuous taoLogPrimitive := by
  have hmul : Continuous (fun x : ℝ ↦ x * Real.log x) :=
    Real.continuous_mul_log
  change Continuous (fun x : ℝ ↦ x - x * Real.log |x|)
  simpa only [Real.log_abs] using! continuous_id.sub hmul

theorem hasDerivAt_taoLogPrimitive {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt taoLogPrimitive (-Real.log |x|) x := by
  have hmul : HasDerivAt (fun y : ℝ ↦ y * Real.log y)
      (Real.log x + 1) x := Real.hasDerivAt_mul_log hx
  have hderiv := (hasDerivAt_id x).sub hmul
  have hderiv' : HasDerivAt (fun y : ℝ ↦ y - y * Real.log y)
      (-Real.log x) x := by
    convert! hderiv using 1
    ring
  unfold taoLogPrimitive
  simpa only [Real.log_abs] using! hderiv'

/-- Exact primitive formula for the logarithmic kernel.  No endpoint
nonvanishing assumptions are needed. -/
theorem intervalIntegral_neg_log_abs (a b : ℝ) :
    (∫ x in a..b, -Real.log |x|) =
      taoLogPrimitive b - taoLogPrimitive a := by
  rw [intervalIntegral.integral_neg]
  rw [show (fun x : ℝ ↦ Real.log |x|) = Real.log by
    funext x
    exact Real.log_abs x]
  rw [integral_log]
  simp only [taoLogPrimitive, Real.log_abs]
  ring

/-- Translating the interval-density potential gives Tao's displayed
difference of primitives. -/
theorem intervalDensityPotential_eq_primitive (a b t : ℝ) :
    (∫ s in a..b, -Real.log |t - s|) =
      taoLogPrimitive (b - t) - taoLogPrimitive (a - t) := by
  calc
    (∫ s in a..b, -Real.log |t - s|) =
        ∫ s in a..b, -Real.log |s - t| := by
      apply intervalIntegral.integral_congr
      intro s _
      change -Real.log |t - s| = -Real.log |s - t|
      rw [abs_sub_comm]
    _ = ∫ x in a - t..b - t, -Real.log |x| := by
      simpa only using!
        (intervalIntegral.integral_comp_sub_right
          (fun x : ℝ ↦ -Real.log |x|) t (a := a) (b := b))
    _ = taoLogPrimitive (b - t) - taoLogPrimitive (a - t) :=
      intervalIntegral_neg_log_abs (a - t) (b - t)

/-- A point mass at zero together with a constant-density interval. -/
def taoPointIntervalTrialPotential (A a b t : ℝ) : ℝ :=
  -Real.log |t| + A * (∫ s in a..b, -Real.log |t - s|)

theorem taoPointIntervalTrialPotential_eq
    (A a b t : ℝ) :
    taoPointIntervalTrialPotential A a b t =
      -Real.log |t| +
        A * (taoLogPrimitive (b - t) - taoLogPrimitive (a - t)) := by
  rw [taoPointIntervalTrialPotential, intervalDensityPotential_eq_primitive]

/-- A point mass at zero, two constant-density intervals, and a point mass
at their common upper endpoint. -/
def taoTwoIntervalEndpointTrialPotential
    (A a B b C M t : ℝ) : ℝ :=
  -Real.log |t| +
    A * (∫ s in a..M, -Real.log |t - s|) +
    B * (∫ s in b..M, -Real.log |t - s|) -
    C * Real.log |M - t|

theorem taoTwoIntervalEndpointTrialPotential_eq
    (A a B b C M t : ℝ) :
    taoTwoIntervalEndpointTrialPotential A a B b C M t =
      -Real.log |t| +
        A * (taoLogPrimitive (M - t) - taoLogPrimitive (a - t)) +
        B * (taoLogPrimitive (M - t) - taoLogPrimitive (b - t)) -
        C * Real.log |M - t| := by
  rw [taoTwoIntervalEndpointTrialPotential,
    intervalDensityPotential_eq_primitive,
    intervalDensityPotential_eq_primitive]

/-! ## Exact parameters in Tao's Cases 2 and 3 -/

def taoCaseTwoFloor : ℝ := 7987 / 10000
def taoCaseTwoCenterFloor : ℝ := 17987 / 10000
def taoCaseTwoA : ℝ := 7233 / 10000
def taoCaseTwoLeftEndpoint : ℝ := 1134371 / 500000

def taoCaseThreeInputFloor : ℝ := 953 / 1250
def taoCaseThreeInputCeiling : ℝ := 27987 / 10000
def taoCaseThreeCenterFloor : ℝ := 2203 / 1250
def taoCaseThreeCenterCeiling : ℝ := 17987 / 10000
def taoCaseThreeA : ℝ := 192829 / 1000000
def taoCaseThreeB : ℝ := 28 / 125
def taoCaseThreeC : ℝ := 31 / 200
def taoCaseThreeLeftA : ℝ := 163 / 100
def taoCaseThreeLeftB : ℝ := 1919 / 1000

/-- The scalar function in Tao's equation (2.5). -/
def taoCaseTwoPotential (t : ℝ) : ℝ :=
  -Real.log t +
    taoCaseTwoA *
      (taoLogPrimitive (taoUpperEdge - t) -
        taoLogPrimitive (taoCaseTwoLeftEndpoint - t))

/-- The scalar function in Tao's equation (2.6). -/
def taoCaseThreePotential (t : ℝ) : ℝ :=
  -Real.log t +
    taoCaseThreeA *
      (taoLogPrimitive (taoUpperEdge - t) -
        taoLogPrimitive (taoCaseThreeLeftA - t)) +
    taoCaseThreeB *
      (taoLogPrimitive (taoUpperEdge - t) -
        taoLogPrimitive (taoCaseThreeLeftB - t)) -
    taoCaseThreeC * Real.log |taoUpperEdge - t|

/-- Exact identification of the Case 2 trial measure with (2.5) on its
positive input range. -/
theorem tao_case_two_trial_eq_potential {t : ℝ} (ht : 0 < t) :
    taoPointIntervalTrialPotential taoCaseTwoA
        taoCaseTwoLeftEndpoint taoUpperEdge t =
      taoCaseTwoPotential t := by
  rw [taoPointIntervalTrialPotential_eq]
  simp only [abs_of_pos ht]
  rfl

/-- Exact identification of the Case 3 trial measure with (2.6) on its
positive input range. -/
theorem tao_case_three_trial_eq_potential {t : ℝ} (ht : 0 < t) :
    taoTwoIntervalEndpointTrialPotential
        taoCaseThreeA taoCaseThreeLeftA
        taoCaseThreeB taoCaseThreeLeftB
        taoCaseThreeC taoUpperEdge t =
      taoCaseThreePotential t := by
  rw [taoTwoIntervalEndpointTrialPotential_eq]
  simp only [abs_of_pos ht]
  rfl

/-! ## Geometry of the parameter ranges -/

theorem tao_case_two_center_interval_mem_floor
    {t0 t : ℝ} (ht0 : taoCaseTwoCenterFloor ≤ t0)
    (ht : t ∈ Icc (t0 - 1) (t0 + 1)) :
    taoCaseTwoFloor ≤ t := by
  unfold taoCaseTwoCenterFloor taoCaseTwoFloor at *
  linarith [ht.1]

theorem tao_case_three_center_interval_mem_input
    {t0 t : ℝ}
    (ht0Lower : taoCaseThreeCenterFloor ≤ t0)
    (ht0Upper : t0 ≤ taoCaseThreeCenterCeiling)
    (ht : t ∈ Icc (t0 - 1) (t0 + 1)) :
    t ∈ Icc taoCaseThreeInputFloor taoCaseThreeInputCeiling := by
  unfold taoCaseThreeCenterFloor taoCaseThreeCenterCeiling
    taoCaseThreeInputFloor taoCaseThreeInputCeiling at *
  constructor <;> linarith [ht.1, ht.2]

theorem tao_case_two_reduction
    (hscalar : ∀ t, taoCaseTwoFloor ≤ t → taoCaseTwoPotential t < 0)
    {t0 : ℝ} (ht0 : taoCaseTwoCenterFloor ≤ t0) :
    ∀ t ∈ Icc (t0 - 1) (t0 + 1),
      taoPointIntervalTrialPotential taoCaseTwoA
        taoCaseTwoLeftEndpoint taoUpperEdge t < 0 := by
  intro t ht
  have hfloor := tao_case_two_center_interval_mem_floor ht0 ht
  have htPos : 0 < t := by
    unfold taoCaseTwoFloor at hfloor
    norm_num at hfloor ⊢
    linarith
  rw [tao_case_two_trial_eq_potential htPos]
  exact hscalar t hfloor

theorem tao_case_three_reduction
    (hscalar : ∀ t ∈ Icc taoCaseThreeInputFloor
      taoCaseThreeInputCeiling, taoCaseThreePotential t < 0)
    {t0 : ℝ}
    (ht0Lower : taoCaseThreeCenterFloor ≤ t0)
    (ht0Upper : t0 ≤ taoCaseThreeCenterCeiling) :
    ∀ t ∈ Icc (t0 - 1) (t0 + 1),
      taoTwoIntervalEndpointTrialPotential
        taoCaseThreeA taoCaseThreeLeftA
        taoCaseThreeB taoCaseThreeLeftB
        taoCaseThreeC taoUpperEdge t < 0 := by
  intro t ht
  have hinput := tao_case_three_center_interval_mem_input
    ht0Lower ht0Upper ht
  have htPos : 0 < t := by
    unfold taoCaseThreeInputFloor at hinput
    norm_num at hinput ⊢
    linarith
  rw [tao_case_three_trial_eq_potential htPos]
  exact hscalar t hinput

end

end Erdos1038
