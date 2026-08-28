import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsCuspOrder
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Reading cusp order from an actual analytic chart coefficient

A chart coefficient analytic at the filled cusp and zero there is
divisible by the actual cusp parameter. The divided slope constructs
the analytic factor. The constant-scaling lemmas account for the
source normalization `s = z / width` without changing the vanishing
order required by the scalar differential theorems.
-/

noncomputable section

open Filter Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods.Triangle

/-- A genuine analytic chart coefficient which vanishes at the filled
cusp supplies first order in the actual exponential parameter. -/
theorem HasCuspOrder.of_eventually_comp {f : ℍ → ℂ} {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (he : ∀ᶠ z in atImInfty, f z = F (cuspQ z)) : HasCuspOrder 1 f := by
  refine ⟨dslope F 0, hF.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt, ?_⟩
  filter_upwards [he] with z hz
  rw [hz, pow_one]
  simpa only [sub_zero, hF0, smul_eq_mul] using (sub_smul_dslope F 0 (cuspQ z)).symm

/-- Dividing a coefficient by a nonzero constant preserves its actual
analytic cusp order. -/
theorem HasCuspOrder.of_const_mul {n : ℕ} {f : ℍ → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hf : HasCuspOrder n (fun z => c * f z)) : HasCuspOrder n f := by
  obtain ⟨F, hF, he⟩ := hf
  refine ⟨fun q => F q / c, hF.div_const, ?_⟩
  filter_upwards [he] with z hz
  apply mul_left_cancel₀ hc
  rw [hz]
  field_simp [hc]

theorem HasCuspOrder.of_eventually_scaled_comp {f : ℍ → ℂ} {F : ℂ → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (he : ∀ᶠ z in atImInfty, c * f z = F (cuspQ z)) : HasCuspOrder 1 f :=
  HasCuspOrder.of_const_mul hc (HasCuspOrder.of_eventually_comp hF hF0 he)

/-- An analytic vanishing coefficient in the normalized source coordinate
`s = z / width` gives the required first order for the `dz` coefficient. -/
theorem hasCuspOrder_one_of_normalized_cusp {f : ℍ → ℂ} {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hF0 : F 0 = 0)
    (he : ∀ᶠ z in atImInfty, (width : ℂ) * f z = F (cuspQ z)) :
    HasCuspOrder 1 f :=
  HasCuspOrder.of_eventually_scaled_comp (Complex.ofReal_ne_zero.mpr width_ne_zero) hF hF0 he

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
