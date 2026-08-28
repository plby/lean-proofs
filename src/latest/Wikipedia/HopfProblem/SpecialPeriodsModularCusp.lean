import Wikipedia.HopfProblem.SpecialPeriodsModular
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.DSlope

/-!
# The normalized inverse cusp coordinate

The simple pole of the actual modular j-function gives the analytic map
`t_c(q) = 1728 / j(q) = 1728 q / modularJUnit q` near zero.  Its derivative
at zero is `1728`, so the complex analytic inverse-function theorem constructs
an actual local inverse `q(t_c)`.  We prove `q(t_c) = t_c u₁(t_c)`, where `u₁`
is analytic and nonvanishing near zero and `u₁(0) = 1/1728`.

This supplies the cusp-coordinate analytic ingredient in Proposition 3.6;
it does not assume the existence of the global lift tau.
-/

noncomputable section

open Filter Topology

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The base cusp coordinate as an analytic function of the modular q-coordinate. -/
def modularCuspBase (q : ℂ) : ℂ := 1728 * q / modularJUnit q

@[simp] theorem modularCuspBase_zero : modularCuspBase 0 = 0 := by
  simp [modularCuspBase]

theorem modularCuspBase_analyticAt_zero : AnalyticAt ℂ modularCuspBase 0 :=
  (analyticAt_const.mul analyticAt_id).div modularJUnit_analyticAt_zero (by simp)

theorem modularCuspBase_hasDerivAt : HasDerivAt modularCuspBase 1728 0 := by
  have hn : HasDerivAt (fun q : ℂ => 1728 * q) 1728 0 := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id (0 : ℂ)).const_mul (1728 : ℂ)
  have hu : HasDerivAt modularJUnit (deriv modularJUnit 0) 0 :=
    modularJUnit_analyticAt_zero.differentiableAt.hasDerivAt
  have hd := hn.div hu (by simp : modularJUnit 0 ≠ 0)
  change HasDerivAt modularCuspBase
    ((1728 * modularJUnit 0 - (1728 * (0 : ℂ)) * deriv modularJUnit 0) / modularJUnit 0 ^ 2) 0 at hd
  simpa only [modularJUnit_zero, mul_one, mul_zero, zero_mul, sub_zero, one_pow, div_one] using hd

theorem modularCuspBase_deriv : deriv modularCuspBase 0 = 1728 :=
  modularCuspBase_hasDerivAt.deriv

theorem modularCuspBase_deriv_ne_zero : deriv modularCuspBase 0 ≠ 0 := by
  rw [modularCuspBase_deriv]
  norm_num

/-- The actual inverse given by the complex analytic inverse-function theorem. -/
def modularCuspQ : ℂ → ℂ :=
  modularCuspBase_analyticAt_zero.hasStrictDerivAt.localInverse
    modularCuspBase (deriv modularCuspBase 0) 0 modularCuspBase_deriv_ne_zero

theorem modularCuspQ_analyticAt_zero : AnalyticAt ℂ modularCuspQ 0 := by
  simpa only [modularCuspQ, modularCuspBase_zero] using
    modularCuspBase_analyticAt_zero.analyticAt_localInverse modularCuspBase_deriv_ne_zero

theorem modularCuspQ_eventually_left_inverse :
    ∀ᶠ q in 𝓝 (0 : ℂ), modularCuspQ (modularCuspBase q) = q :=
  modularCuspBase_analyticAt_zero.hasStrictDerivAt.eventually_left_inverse
    modularCuspBase_deriv_ne_zero

theorem modularCuspQ_eventually_right_inverse :
    ∀ᶠ t in 𝓝 (0 : ℂ), modularCuspBase (modularCuspQ t) = t := by
  simpa only [modularCuspQ, modularCuspBase_zero] using
    modularCuspBase_analyticAt_zero.hasStrictDerivAt.eventually_right_inverse
      modularCuspBase_deriv_ne_zero

@[simp] theorem modularCuspQ_zero : modularCuspQ 0 = 0 := by
  simpa only [modularCuspBase_zero] using modularCuspQ_eventually_left_inverse.self_of_nhds

theorem modularCuspQ_hasDerivAt : HasDerivAt modularCuspQ (1 / 1728) 0 := by
  simpa only [modularCuspQ, modularCuspBase_zero, modularCuspBase_deriv, one_div] using
    (modularCuspBase_analyticAt_zero.hasStrictDerivAt.to_localInverse
      modularCuspBase_deriv_ne_zero).hasDerivAt

theorem modularCuspQ_deriv : deriv modularCuspQ 0 = 1 / 1728 :=
  modularCuspQ_hasDerivAt.deriv

/-- The unit factor in the source's formula `q = t_c u₁(t_c)`. -/
def modularCuspUnit : ℂ → ℂ := dslope modularCuspQ 0

theorem modularCuspUnit_analyticAt_zero : AnalyticAt ℂ modularCuspUnit 0 :=
  modularCuspQ_analyticAt_zero.hasFPowerSeriesAt.has_fpower_series_dslope_fslope.analyticAt

@[simp] theorem modularCuspUnit_zero : modularCuspUnit 0 = 1 / 1728 := by
  rw [modularCuspUnit, dslope_same, modularCuspQ_deriv]

/-- The unit factor is an actual analytic function, with an exact factorization. -/
theorem modularCuspQ_eq_mul_unit (t : ℂ) : modularCuspQ t = t * modularCuspUnit t := by
  simpa only [modularCuspUnit, sub_zero, modularCuspQ_zero, smul_eq_mul] using
    (sub_smul_dslope modularCuspQ 0 t).symm

theorem modularCuspUnit_eventually_ne_zero :
    ∀ᶠ t in 𝓝 (0 : ℂ), modularCuspUnit t ≠ 0 :=
  modularCuspUnit_analyticAt_zero.continuousAt.eventually_ne (by simp)

theorem modularCuspQ_eventually_norm_lt_one :
    ∀ᶠ t in 𝓝 (0 : ℂ), ‖modularCuspQ t‖ < 1 := by
  have h := modularCuspQ_analyticAt_zero.continuousAt.preimage_mem_nhds
    (show Metric.ball (0 : ℂ) 1 ∈ 𝓝 (modularCuspQ 0) by
      rw [modularCuspQ_zero]
      exact Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)
  filter_upwards [h] with t ht
  simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using ht

theorem modularCuspQ_order : analyticOrderAt modularCuspQ 0 = 1 :=
  modularCuspQ_analyticAt_zero.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    modularCuspQ_zero (by rw [modularCuspQ_deriv]; norm_num)

/-- On a punctured neighborhood, the inverse satisfies exactly the source's
normalization `j = 1728/t_c`. -/
theorem modularCuspQ_eventually_j_eq :
    ∀ᶠ t in 𝓝[≠] (0 : ℂ), modularJInQ (modularCuspQ t) = 1728 / t := by
  filter_upwards [modularCuspQ_eventually_right_inverse.filter_mono nhdsWithin_le_nhds,
    modularCuspUnit_eventually_ne_zero.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t ht hu ht₀
  have ht₀' : t ≠ 0 := ht₀
  have hq : modularCuspQ t ≠ 0 := by rw [modularCuspQ_eq_mul_unit]; exact mul_ne_zero ht₀' hu
  have hj : modularJUnit (modularCuspQ t) ≠ 0 := by
    intro h
    simp [modularCuspBase, h] at ht
    exact ht₀' ht.symm
  unfold modularCuspBase at ht
  unfold modularJInQ
  rw [eq_div_iff ht₀']
  calc
    modularJUnit (modularCuspQ t) / modularCuspQ t * t =
        modularJUnit (modularCuspQ t) / modularCuspQ t *
          (1728 * modularCuspQ t / modularJUnit (modularCuspQ t)) :=
      congrArg (fun v => modularJUnit (modularCuspQ t) / modularCuspQ t * v) ht.symm
    _ = 1728 := by field_simp

/-- A positive disc on which the actual inverse q-coordinate and its
nonvanishing unit factor are holomorphic and satisfy the normalized j equation. -/
theorem exists_modular_cusp_coordinate :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ modularCuspQ (Metric.ball 0 r) ∧
      AnalyticOnNhd ℂ modularCuspUnit (Metric.ball 0 r) ∧
      ∀ t ∈ Metric.ball (0 : ℂ) r,
        modularCuspUnit t ≠ 0 ∧ ‖modularCuspQ t‖ < 1 ∧
        modularCuspQ t = t * modularCuspUnit t ∧
        (t ≠ 0 → modularJInQ (modularCuspQ t) = 1728 / t) := by
  have hj : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 → modularJInQ (modularCuspQ t) = 1728 / t :=
    eventually_nhdsWithin_iff.mp modularCuspQ_eventually_j_eq
  have hall : ∀ᶠ t in 𝓝 (0 : ℂ),
      AnalyticAt ℂ modularCuspQ t ∧ AnalyticAt ℂ modularCuspUnit t ∧
      modularCuspUnit t ≠ 0 ∧ ‖modularCuspQ t‖ < 1 ∧
      (t ≠ 0 → modularJInQ (modularCuspQ t) = 1728 / t) := by
    filter_upwards [modularCuspQ_analyticAt_zero.eventually_analyticAt,
      modularCuspUnit_analyticAt_zero.eventually_analyticAt,
      modularCuspUnit_eventually_ne_zero, modularCuspQ_eventually_norm_lt_one, hj]
      with t hq hu hne hn hjt
    exact ⟨hq, hu, hne, hn, hjt⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨r, hr, fun t ht => (hball ht).1, fun t ht => (hball ht).2.1, ?_⟩
  intro t ht
  exact ⟨(hball ht).2.2.1, (hball ht).2.2.2.1, modularCuspQ_eq_mul_unit t,
    (hball ht).2.2.2.2⟩

theorem modularCuspBase_eq_div_j (q : ℂ) : modularCuspBase q = 1728 / modularJInQ q := by
  rw [modularCuspBase, modularJInQ, div_div_eq_mul_div]

/-- The modular function is one-to-one in a sufficiently small q-disc.
This is the one-sheet input for the global modular-quotient argument. -/
theorem modularJInQ_injOn_small_disc :
    ∃ r : ℝ, 0 < r ∧ Set.InjOn modularJInQ (Metric.ball 0 r) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp modularCuspQ_eventually_left_inverse
  refine ⟨r, hr, ?_⟩
  intro q hq w hw he
  calc
    q = modularCuspQ (modularCuspBase q) := (hball hq).symm
    _ = modularCuspQ (modularCuspBase w) := by
      rw [modularCuspBase_eq_div_j, he, ← modularCuspBase_eq_div_j]
    _ = w := hball hw

end Wikipedia.HopfProblem.SpecialPeriods
