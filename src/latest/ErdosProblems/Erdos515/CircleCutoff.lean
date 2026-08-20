import ErdosProblems.Erdos515.Prawitz

/-!
# A compactly supported three-period boundary cutoff

This file packages the elementary cutoff used when a periodic boundary function on the circle is
fed to a real-line maximal inequality.  Three adjacent periods are retained: this is enough to
contain every interval of angular radius `π` whose centre belongs to the standard angular
interval.
-/

open MeasureTheory Set

open scoped ENNReal Real

namespace Erdos515.Prawitz

/-- The nonnegative boundary data induced by `q` on the circle of radius `R`. -/
noncomputable def boundaryNorm (q : ℂ → ℂ) (R : ℝ) (θ : ℝ) : ℝ :=
  ‖q (circlePoint R θ)‖

/-- The interval consisting of three consecutive copies of `angularInterval`. -/
def threePeriodInterval : Set ℝ := Ioc (-2 * Real.pi) (4 * Real.pi)

/-- Keep three periods of the boundary data and extend by zero to the real line. -/
noncomputable def threePeriodCutoff (q : ℂ → ℂ) (R : ℝ) : ℝ → ℝ≥0∞ :=
  threePeriodInterval.indicator (fun θ => ENNReal.ofReal (boundaryNorm q R θ))

lemma continuous_boundaryNorm {q : ℂ → ℂ} (hq : Continuous q) (R : ℝ) :
    Continuous (boundaryNorm q R) := by
  apply Continuous.norm
  apply hq.comp
  unfold circlePoint
  fun_prop

lemma periodic_boundaryNorm (q : ℂ → ℂ) (R : ℝ) :
    Function.Periodic (boundaryNorm q R) (2 * Real.pi) := by
  intro θ
  unfold boundaryNorm circlePoint
  congr 2
  simp only [Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * Real.pi * Complex.I by
    push_cast
    rfl]
  rw [Complex.exp_two_pi_mul_I, mul_one]

theorem measurable_threePeriodCutoff {q : ℂ → ℂ} {R : ℝ}
    (hboundary : Continuous (boundaryNorm q R)) :
    Measurable (threePeriodCutoff q R) := by
  unfold threePeriodCutoff
  exact hboundary.measurable.ennreal_ofReal.indicator measurableSet_Ioc

/-- A window of angular radius `π` around a point in the standard angular interval lies inside
the three-period cutoff. -/
lemma Icc_sub_add_pi_subset_threePeriodInterval {θ : ℝ} (hθ : θ ∈ angularInterval) :
    Icc (θ - Real.pi) (θ + Real.pi) ⊆ threePeriodInterval := by
  intro x hx
  rw [angularInterval] at hθ
  rw [threePeriodInterval]
  constructor
  · calc
      -2 * Real.pi < θ - Real.pi := by linarith [Real.pi_pos, hθ.1]
      _ ≤ x := hx.1
  · calc
      x ≤ θ + Real.pi := hx.2
      _ ≤ 3 * Real.pi := by linarith [hθ.2]
      _ ≤ 4 * Real.pi := by linarith [Real.pi_pos]

/-- On every angular-radius-`π` window centred in `angularInterval`, the cutoff agrees with the
original boundary norm. -/
theorem threePeriodCutoff_eq_boundaryNorm {q : ℂ → ℂ} {R θ x : ℝ}
    (hθ : θ ∈ angularInterval) (hx : x ∈ Icc (θ - Real.pi) (θ + Real.pi)) :
    threePeriodCutoff q R x = ENNReal.ofReal (boundaryNorm q R x) := by
  rw [threePeriodCutoff, indicator_of_mem
    (Icc_sub_add_pi_subset_threePeriodInterval hθ hx)]

/-- The total mass of the three-period cutoff is at most three times a one-period integral bound.

The hypothesis is deliberately stated using the same real set integral over `angularInterval`
that occurs in the Hardy bound. -/
theorem lintegral_threePeriodCutoff_le {q : ℂ → ℂ} {R C : ℝ}
    (hboundary : Continuous (boundaryNorm q R))
    (hC : (∫ θ in angularInterval, boundaryNorm q R θ) ≤ C) :
    (∫⁻ θ : ℝ, threePeriodCutoff q R θ) ≤ 3 * ENNReal.ofReal C := by
  let v : ℝ → ℝ := boundaryNorm q R
  have hv : Continuous v := hboundary
  have hv_nonneg : ∀ x, 0 ≤ v x := fun x => norm_nonneg _
  have hv_periodic : Function.Periodic v (2 * Real.pi) := periodic_boundaryNorm q R
  have hv_intervalIntegrable : ∀ a b : ℝ, IntervalIntegrable v volume a b := by
    intro a b
    exact hv.intervalIntegrable (μ := volume) a b
  have hbase : (∫ x in (0 : ℝ)..2 * Real.pi, v x) ≤ C := by
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
    simpa only [v, angularInterval] using hC
  have hperiod :
      (∫ x in (-2 * Real.pi)..0, v x) = ∫ x in (0 : ℝ)..2 * Real.pi, v x := by
    convert hv_periodic.intervalIntegral_add_eq (-2 * Real.pi) 0 using 1 <;> ring
  have hthree :
      (∫ x in (-2 * Real.pi)..4 * Real.pi, v x) =
        3 * ∫ x in (0 : ℝ)..2 * Real.pi, v x := by
    have hmany := hv_periodic.intervalIntegral_add_zsmul_eq (3 : ℤ)
      (-2 * Real.pi) hv_intervalIntegrable
    have hperiod' :
        (∫ x in (-2 * Real.pi)..(-2 * Real.pi + 2 * Real.pi), v x) =
          ∫ x in (0 : ℝ)..2 * Real.pi, v x := by
      convert hperiod using 1 <;> ring
    rw [hperiod'] at hmany
    convert hmany using 1 <;> norm_num <;> ring
  have hthree_le : (∫ x in threePeriodInterval, v x) ≤ 3 * C := by
    rw [threePeriodInterval, ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos] : (-2 * Real.pi : ℝ) ≤ 4 * Real.pi)]
    rw [hthree]
    exact mul_le_mul_of_nonneg_left hbase (by norm_num)
  have hv_integrable : IntegrableOn v threePeriodInterval := by
    rw [threePeriodInterval]
    exact (hv.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hlintegral_period :
      (∫⁻ x in threePeriodInterval, ENNReal.ofReal (v x)) =
        ENNReal.ofReal (∫ x in threePeriodInterval, v x) := by
    exact (ofReal_integral_eq_lintegral_ofReal hv_integrable
      (Filter.Eventually.of_forall hv_nonneg)).symm
  rw [threePeriodCutoff]
  rw [MeasureTheory.lintegral_indicator (s := threePeriodInterval)
    (by simpa only [threePeriodInterval] using measurableSet_Ioc)]
  change (∫⁻ x in threePeriodInterval, ENNReal.ofReal (v x)) ≤ _
  rw [hlintegral_period]
  calc
    ENNReal.ofReal (∫ x in threePeriodInterval, v x) ≤ ENNReal.ofReal (3 * C) :=
      ENNReal.ofReal_le_ofReal hthree_le
    _ = 3 * ENNReal.ofReal C := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num

end Erdos515.Prawitz
