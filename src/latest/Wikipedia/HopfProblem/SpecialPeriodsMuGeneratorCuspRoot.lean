import Wikipedia.HopfProblem.SpecialPeriodsModularLocalChartsRoots

/-!
# The normalized analytic square root of a cusp unit

An analytic function taking the value `1` at the cusp admits a local
analytic square root with the same normalization.  We construct it from
the analytic inverse theorem for the power map, using the existing
analytic-unit root theorem, and divide by its value at the center.
-/

noncomputable section

open Filter Set Metric
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.MuGenerator

/-- An analytic unit with value `1` has an analytic square-root germ
whose value is exactly `1`, not just an unspecified square root of `1`. -/
theorem exists_analytic_sqrt_germ_one {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0) (h0 : h 0 = 1) :
    ∃ b : ℂ → ℂ, AnalyticAt ℂ b 0 ∧ b 0 = 1 ∧
      ∀ᶠ t in 𝓝 0, b t ^ 2 = h t := by
  obtain ⟨r, hr, hr0, hrpow⟩ :=
    exists_analytic_unit_root hh (by simp [h0]) (by norm_num : 0 < (2 : ℕ))
  have hr02 : r 0 ^ 2 = 1 := by simpa only [h0] using hrpow.self_of_nhds
  refine ⟨fun t => r t / r 0, hr.div analyticAt_const hr0, div_self hr0, ?_⟩
  filter_upwards [hrpow] with t ht
  simp only [div_pow, hr02, div_one, ht]

/-- The normalized square root is analytic and nonvanishing on an
actual positive-radius disc, where its square equals the original function. -/
theorem exists_analytic_sqrt_ball_one {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0) (h0 : h 0 = 1) :
    ∃ ε > 0, ∃ b : ℂ → ℂ, AnalyticOnNhd ℂ b (ball 0 ε) ∧ b 0 = 1 ∧
      (∀ t ∈ ball 0 ε, b t ≠ 0) ∧ EqOn (fun t => b t ^ 2) h (ball 0 ε) := by
  obtain ⟨b, hb, hb0, hbpow⟩ := exists_analytic_sqrt_germ_one hh h0
  have hbne : ∀ᶠ t in 𝓝 0, b t ≠ 0 :=
    hb.continuousAt.eventually_ne (by simp [hb0])
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (hb.eventually_analyticAt.and (hbne.and hbpow))
  refine ⟨ε, hε, b, ?_, hb0, ?_, ?_⟩
  · exact fun t ht => (hball ht).1
  · exact fun t ht => (hball ht).2.1
  · exact fun t ht => (hball ht).2.2

end Wikipedia.HopfProblem.SpecialPeriods.MuGenerator
