import Wikipedia.HopfProblem.SpecialPeriodsConstructionAdmissible
import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyData

/-!
# Actual cusp-family data for the constructed admissible periods

The constructed global functions supply all three analytic cusp germs.
Their proved analytic estimates give a genuine positive small-drift
radius.  Shrinking that radius makes the logarithmic cusp-family periods
agree with the actual globally admissible period functions everywhere
over the corresponding punctured cusp disc.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Construction.PeriodFunctions

open ToricSpace CuspUniformization

variable (F : PeriodFunctions)

/-- The globally constructed admissible periods determine honest local
cusp-family data, including the analytic and small-drift bounds and the
exact period-point identification on the entire small cusp region. -/
theorem exists_cusp_data :
    ∃ C : CuspFamily.Data, ∀ z : ℍ, ‖Triangle.cuspQ z‖ < C.radius →
      (F.admissiblePeriods.point z).val =
        cuspPeriodPoint C.μ C.b C.h ((z : ℂ) / Triangle.width) := by
  obtain ⟨h, hh, hτ⟩ := F.tau_cusp
  obtain ⟨m, hm, hμ⟩ := F.mu_cusp
  obtain ⟨b, hb, hβ⟩ := F.admissiblePeriods_beta_cusp
  have hβ' : ∀ᶠ z in atImInfty,
      (F.beta z + F.shiftConstant) + (F.data.tau z : ℂ) = b (Triangle.cuspQ z) := by
    simpa only [admissiblePeriods_beta, admissiblePeriods_tau] using hβ
  have hpoint : ∀ᶠ z in atImInfty,
      (F.admissiblePeriods.point z).val =
        cuspPeriodPoint m b h ((z : ℂ) / Triangle.width) :=
    periodPoint_eventually_eq_cuspPeriodPoint hτ hμ hβ'
  obtain ⟨ε, hε, hε1, hR, hC⟩ :=
    exists_cuspCorrection_admissible_radius_of_analyticAt hm hb hh
  obtain ⟨r, hr, hrε, hmatch⟩ := eventual_cuspQ_radius_lt hε hpoint
  refine ⟨{
    μ := m
    b := b
    h := h
    radius := r
    radius_pos := hr
    radius_lt_one := hrε.trans hε1
    holomorphic := fun i j => (hC i j).mono (Metric.ball_subset_ball hrε.le)
    smallDrift := fun t ht0 htr => hR t ht0 (htr.trans hrε) }, hmatch⟩

/-- A choice of the actual cusp-family data constructed from the global
admissible special period functions. -/
def cuspData : CuspFamily.Data := F.exists_cusp_data.choose

/-- Exact agreement of all three actual period entries throughout the
chosen punctured cusp region. -/
theorem cuspData_periodPoint (z : ℍ) (hz : ‖Triangle.cuspQ z‖ < F.cuspData.radius) :
    (F.admissiblePeriods.point z).val =
      cuspPeriodPoint F.cuspData.μ F.cuspData.b F.cuspData.h
        ((z : ℂ) / Triangle.width) :=
  F.exists_cusp_data.choose_spec z hz

/-- The actual period block equals the cusp family's logarithmic period
matrix with no change of signs, generators, or cusp normalization. -/
theorem cuspData_leftBlock (z : ℍ) (hz : ‖Triangle.cuspQ z‖ < F.cuspData.radius) :
    (F.admissiblePeriods.point z).val.leftBlock =
      logarithmicPeriod F.cuspData.correction ((z : ℂ) / Triangle.width) := by
  rw [F.cuspData_periodPoint z hz, cuspPeriodPoint_leftBlock]

/-- The correction matrix in the original exponential cusp coordinate,
separated from the explicit logarithmic monodromy term. -/
theorem cuspData_leftBlock_expanded (z : ℍ)
    (hz : ‖Triangle.cuspQ z‖ < F.cuspData.radius) :
    (F.admissiblePeriods.point z).val.leftBlock =
      ((z : ℂ) / Triangle.width) • B₀.map (Int.castRingHom ℂ) +
        F.cuspData.correction (Triangle.cuspQ z) := by
  rw [F.cuspData_leftBlock z hz, logarithmicPeriod, exponential_normalized_eq_cuspQ]

end Wikipedia.HopfProblem.SpecialPeriods.Construction.PeriodFunctions
