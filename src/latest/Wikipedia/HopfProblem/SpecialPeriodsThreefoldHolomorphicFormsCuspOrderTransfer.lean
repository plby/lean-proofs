import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsCuspLogCover
import Wikipedia.HopfProblem.SpecialPeriodsCuspGlobalOverlapBase
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspOrderChart

/-!
# From the actual logarithmic cusp disc to the source cusp filter

Every sufficiently high upper-half-plane point belongs to the original
chosen cusp overlap. Its logarithm is exactly `z / width`, and its
regular-base image is the original point. Thus identities proved on
the actual logarithmic cover give the stated analytic cusp order on
the original upper half-plane, with no new overlap or domain premise.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp

open Triangle CuspUniformization CuspFamily CuspGlobalOverlap
open TriangleHolomorphicDifferentials

theorem actual_radius_le_cuspRadius : CuspGeometry.data.radius ≤ cuspRadius width :=
  specialBaseCover_cusp_radius_bounds.2.2.le

/-- The actual regular base point of a logarithmic cusp parameter. -/
def cuspRegularBase (s : LogBase CuspGeometry.data.radius) : TriangleRegularPoint :=
  logBaseToRegular CuspGeometry.data.radius actual_radius_le_cuspRadius s

@[simp] theorem cuspRegularBase_coe (s : LogBase CuspGeometry.data.radius) :
    ((cuspRegularBase s : ℍ) : ℂ) = (width : ℂ) * (s : ℂ) :=
  logBaseToRegular_coe CuspGeometry.data.radius actual_radius_le_cuspRadius s

@[simp] theorem cuspQ_cuspRegularBase (s : LogBase CuspGeometry.data.radius) :
    cuspQ (cuspRegularBase s) = exponential s :=
  logBaseToRegular_cuspQ CuspGeometry.data.radius actual_radius_le_cuspRadius s

/-- Sufficiently high points lie in the actual small cusp coordinate disc. -/
theorem eventually_mem_actual_cusp :
    ∀ᶠ z in atImInfty, ‖cuspQ z‖ < CuspGeometry.data.radius := by
  have hq : Tendsto cuspQ atImInfty (𝓝 (0 : ℂ)) :=
    cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds
  have h := hq.eventually (Metric.ball_mem_nhds (0 : ℂ) CuspGeometry.data.radius_pos)
  simpa only [Metric.mem_ball, dist_zero_right] using h

/-- The genuine logarithmic parameter of any point in this overlap. -/
def actualLogBase (z : ℍ) (hz : ‖cuspQ z‖ < CuspGeometry.data.radius) :
    LogBase CuspGeometry.data.radius :=
  ⟨(z : ℂ) / width, by
    rw [mem_logBase, exponential_div_width]
    exact hz⟩

@[simp] theorem actualLogBase_coe (z : ℍ) (hz : ‖cuspQ z‖ < CuspGeometry.data.radius) :
    (actualLogBase z hz : ℂ) = (z : ℂ) / width := rfl

@[simp] theorem exponential_actualLogBase (z : ℍ)
    (hz : ‖cuspQ z‖ < CuspGeometry.data.radius) :
    exponential (actualLogBase z hz) = cuspQ z := exponential_div_width z

/-- No point is changed by passing to its actual logarithm and back. -/
theorem cuspRegularBase_actualLogBase (z : ℍ)
    (hz : ‖cuspQ z‖ < CuspGeometry.data.radius) :
    (cuspRegularBase (actualLogBase z hz) : ℍ) = z := by
  apply UpperHalfPlane.ext
  rw [cuspRegularBase_coe, actualLogBase_coe]
  field_simp [Complex.ofReal_ne_zero.mpr width_ne_zero]

/-- An analytic vanishing coefficient established on the actual logarithmic
cover gives first cusp order in the original source parameter. -/
theorem hasCuspOrder_one_of_log_coordinate {f : ℍ → ℂ} {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (he : ∀ s : LogBase CuspGeometry.data.radius,
      f (cuspRegularBase s) = F (exponential s)) : HasCuspOrder 1 f := by
  apply HasCuspOrder.of_eventually_comp hF hF0
  filter_upwards [eventually_mem_actual_cusp] with z hz
  have h := he (actualLogBase z hz)
  rw [cuspRegularBase_actualLogBase, exponential_actualLogBase] at h
  exact h

/-- The exact constant base-coordinate normalization preserves the proved order. -/
theorem hasCuspOrder_one_of_scaled_log_coordinate {f : ℍ → ℂ} {F : ℂ → ℂ} {a : ℂ}
    (ha : a ≠ 0) (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (he : ∀ s : LogBase CuspGeometry.data.radius,
      a * f (cuspRegularBase s) = F (exponential s)) : HasCuspOrder 1 f :=
  HasCuspOrder.of_const_mul ha (hasCuspOrder_one_of_log_coordinate hF hF0 he)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.Cusp
