import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Scalar exponential transport on a real interval

These are the actual exponential integrals used for rank-one parallel
transport. Nonvanishing is unconditional; composition uses the ordinary
interval-integrability conditions required to split the integral.
-/

noncomputable section

open Set MeasureTheory

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

/-- Transport for the scalar differential equation `s' + β s = 0`. -/
def scalarTransport (β : ℝ → ℂ) (a b : ℝ) : ℂ :=
  Complex.exp (-(∫ t in a..b, β t))

theorem scalarTransport_ne_zero (β : ℝ → ℂ) (a b : ℝ) :
    scalarTransport β a b ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem scalarTransport_self (β : ℝ → ℂ) (a : ℝ) :
    scalarTransport β a a = 1 := by simp [scalarTransport]

theorem scalarTransport_reverse (β : ℝ → ℂ) (a b : ℝ) :
    scalarTransport β b a = (scalarTransport β a b)⁻¹ := by
  unfold scalarTransport
  rw [intervalIntegral.integral_symm a b, neg_neg, Complex.exp_neg, inv_inv]

/-- Composition is in the order of the induced fibre maps. -/
theorem scalarTransport_comp (β : ℝ → ℂ) (a b c : ℝ)
    (hab : IntervalIntegrable β volume a b) (hbc : IntervalIntegrable β volume b c) :
    scalarTransport β a c = scalarTransport β b c * scalarTransport β a b := by
  simp only [scalarTransport]
  rw [← intervalIntegral.integral_add_adjacent_intervals hab hbc, neg_add, Complex.exp_add]
  exact mul_comm _ _

theorem scalarTransport_congr {β δ : ℝ → ℂ} {a b : ℝ}
    (h : EqOn β δ (uIcc a b)) : scalarTransport β a b = scalarTransport δ a b := by
  unfold scalarTransport
  rw [intervalIntegral.integral_congr h]

/-- The same actual exponential transport as an invertible complex scalar. -/
def scalarTransportUnit (β : ℝ → ℂ) (a b : ℝ) : ℂˣ :=
  Units.mk0 (scalarTransport β a b) (scalarTransport_ne_zero β a b)

@[simp] theorem scalarTransportUnit_coe (β : ℝ → ℂ) (a b : ℝ) :
    (scalarTransportUnit β a b : ℂ) = scalarTransport β a b := rfl

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
