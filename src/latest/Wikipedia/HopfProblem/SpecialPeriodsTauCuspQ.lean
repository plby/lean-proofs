import Wikipedia.HopfProblem.SpecialPeriodsModularCusp

/-!
# The actual modular q-lift of a simple pole

For a holomorphic nonvanishing numerator `a`, the function `a(t)/t` has an
actual modular q-lift near zero. It is obtained by substituting `1728*t/a(t)`
in the inverse cusp chart, not by postulating a root or a cusp expansion.
The resulting q-coordinate has the exact form `t * u(t)`, with
`u(0) = 1/a(0)` and vanishing order one.
-/

noncomputable section

open Filter Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

/-- The normalized base coordinate of the simple pole `a(t)/t`. -/
def simplePoleCoordinate (a : ℂ → ℂ) (t : ℂ) : ℂ := 1728 * t / a t

/-- The actual q-coordinate obtained from the analytic inverse cusp chart. -/
def simplePoleQ (a : ℂ → ℂ) (t : ℂ) : ℂ :=
  modularCuspQ (simplePoleCoordinate a t)

/-- The nonzero holomorphic factor of the actual q-lift. -/
def simplePoleUnit (a : ℂ → ℂ) (t : ℂ) : ℂ :=
  (1728 / a t) * modularCuspUnit (simplePoleCoordinate a t)

@[simp] theorem simplePoleCoordinate_zero (a : ℂ → ℂ) :
    simplePoleCoordinate a 0 = 0 := by simp [simplePoleCoordinate]

@[simp] theorem simplePoleQ_zero (a : ℂ → ℂ) : simplePoleQ a 0 = 0 := by
  simp [simplePoleQ]

@[simp] theorem simplePoleUnit_zero (a : ℂ → ℂ) :
    simplePoleUnit a 0 = 1 / a 0 := by
  simp [simplePoleUnit]
  ring

theorem simplePoleCoordinate_analyticAt {a : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) :
    AnalyticAt ℂ (simplePoleCoordinate a) 0 :=
  (analyticAt_const.mul analyticAt_id).div ha ha0

theorem simplePoleQ_analyticAt {a : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) : AnalyticAt ℂ (simplePoleQ a) 0 := by
  have hq : AnalyticAt ℂ modularCuspQ (simplePoleCoordinate a 0) := by
    simpa only [simplePoleCoordinate_zero] using modularCuspQ_analyticAt_zero
  exact hq.comp (simplePoleCoordinate_analyticAt ha ha0)

theorem simplePoleUnit_analyticAt {a : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) :
    AnalyticAt ℂ (simplePoleUnit a) 0 := by
  have hu : AnalyticAt ℂ modularCuspUnit (simplePoleCoordinate a 0) := by
    simpa only [simplePoleCoordinate_zero] using modularCuspUnit_analyticAt_zero
  exact (analyticAt_const.div ha ha0).mul
    (hu.comp (simplePoleCoordinate_analyticAt ha ha0))

/-- This factorization is an exact identity of the constructed functions. -/
theorem simplePoleQ_eq_mul_unit (a : ℂ → ℂ) (t : ℂ) :
    simplePoleQ a t = t * simplePoleUnit a t := by
  rw [simplePoleQ, modularCuspQ_eq_mul_unit]
  simp only [simplePoleCoordinate, simplePoleUnit]
  ring

theorem simplePoleQ_order {a : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) :
    analyticOrderAt (simplePoleQ a) 0 = 1 := by
  have hu := simplePoleUnit_analyticAt ha ha0
  have he : simplePoleQ a = id * simplePoleUnit a :=
    funext (simplePoleQ_eq_mul_unit a)
  rw [he, analyticOrderAt_mul analyticAt_id hu, analyticOrderAt_id,
    hu.analyticOrderAt_eq_zero.mpr (by simpa using one_div_ne_zero ha0), add_zero]

theorem simplePoleQ_eventually_j_eq {a : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) :
    ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → modularJInQ (simplePoleQ a t) = a t / t := by
  have hj : ∀ᶠ u in 𝓝 (0 : ℂ), u ≠ 0 →
      modularJInQ (modularCuspQ u) = 1728 / u :=
    eventually_nhdsWithin_iff.mp modularCuspQ_eventually_j_eq
  have hc : Tendsto (simplePoleCoordinate a) (𝓝 0) (𝓝 0) := by
    simpa only [simplePoleCoordinate_zero] using
      (simplePoleCoordinate_analyticAt ha ha0).continuousAt.tendsto
  filter_upwards [hc.eventually hj, ha.continuousAt.eventually_ne ha0] with t hjt hat
  intro ht
  have hct : simplePoleCoordinate a t ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) ht) hat
  rw [simplePoleQ, hjt hct, simplePoleCoordinate]
  field_simp

/-- The actual q-lift is holomorphic and satisfies the exact modular
equation on an arbitrarily small target q-disc. -/
theorem exists_simplePoleQ_coordinate {a : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) {R : ℝ} (hR : 0 < R) :
    ∃ r > 0,
      AnalyticOnNhd ℂ (simplePoleQ a) (Metric.ball 0 r) ∧
      AnalyticOnNhd ℂ (simplePoleUnit a) (Metric.ball 0 r) ∧
      ∀ t ∈ Metric.ball (0 : ℂ) r,
        a t ≠ 0 ∧ simplePoleUnit a t ≠ 0 ∧ ‖simplePoleQ a t‖ < R ∧
        (t ≠ 0 → modularJInQ (simplePoleQ a t) = a t / t) := by
  have hq := simplePoleQ_analyticAt ha ha0
  have hu := simplePoleUnit_analyticAt ha ha0
  have hu0 : simplePoleUnit a 0 ≠ 0 := by
    rw [simplePoleUnit_zero]
    exact one_div_ne_zero ha0
  have hn : ∀ᶠ t in 𝓝 (0 : ℂ), ‖simplePoleQ a t‖ < R := by
    have h := hq.continuousAt.preimage_mem_nhds
      (show Metric.ball (0 : ℂ) R ∈ 𝓝 (simplePoleQ a 0) by
        rw [simplePoleQ_zero]
        exact Metric.ball_mem_nhds _ hR)
    filter_upwards [h] with t ht
    simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using ht
  have hall : ∀ᶠ t in 𝓝 (0 : ℂ), AnalyticAt ℂ (simplePoleQ a) t ∧
      AnalyticAt ℂ (simplePoleUnit a) t ∧ a t ≠ 0 ∧ simplePoleUnit a t ≠ 0 ∧
      ‖simplePoleQ a t‖ < R ∧
      (t ≠ 0 → modularJInQ (simplePoleQ a t) = a t / t) := by
    filter_upwards [hq.eventually_analyticAt, hu.eventually_analyticAt,
      ha.continuousAt.eventually_ne ha0,
      hu.continuousAt.eventually_ne hu0,
      hn, simplePoleQ_eventually_j_eq ha ha0] with t hqt hut hat hut0 hnt hjt
    exact ⟨hqt, hut, hat, hut0, hnt, hjt⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  exact ⟨r, hr, fun t ht => (hball ht).1,
    fun t ht => (hball ht).2.1, fun t ht => (hball ht).2.2⟩

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
