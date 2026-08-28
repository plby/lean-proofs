import Wikipedia.HopfProblem.SpecialPeriodsCuspData
import Wikipedia.HopfProblem.SpecialPeriodsTriangleCusp

/-!
# Cusp expansions of the actual special period functions

Analytic cusp remainders imply that the imaginary part of the first period
tends to infinity.  The three actual cusp expansions identify the original
period block with the logarithmic cusp-period matrix, uniformly on a genuine
small punctured disc.  Adding a constant to the third period changes only
its analytic cusp remainder.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Construction

open ToricSpace CuspUniformization

/-- The source cusp coordinate is precisely the exponential of the
normalized logarithmic coordinate used for the toric cusp family. -/
theorem exponential_normalized_eq_cuspQ (z : ℍ) :
    exponential ((z : ℂ) / Triangle.width) = Triangle.cuspQ z := by
  simp only [exponential, Triangle.cuspQ_eq_exp, mul_div_assoc]

/-- An analytic germ evaluated in the actual cusp coordinate has its
ordinary limiting value at zero. -/
theorem cusp_analytic_tendsto {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    Tendsto (fun z : ℍ => f (Triangle.cuspQ z)) atImInfty (𝓝 (f 0)) :=
  hf.continuousAt.tendsto.comp
    (Triangle.cuspQ_tendsto_atImInfty.mono_right nhdsWithin_le_nhds)

/-- The regular part of the first period converges to its cusp value. -/
theorem tau_remainder_tendsto_of_cusp_formula {τ : ℍ → ℍ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0)
    (hτ : ∀ᶠ z in atImInfty,
      (τ z : ℂ) = (z : ℂ) / Triangle.width + h (Triangle.cuspQ z)) :
    Tendsto (fun z : ℍ => (τ z : ℂ) - (z : ℂ) / Triangle.width)
      atImInfty (𝓝 (h 0)) := by
  apply (cusp_analytic_tendsto hh).congr'
  filter_upwards [hτ] with z hz
  rw [hz, add_sub_cancel_left]

/-- The positive cusp width and the analytic remainder prove divergence
of the imaginary part; this is not a separate growth hypothesis. -/
theorem tau_im_tendsto_atTop_of_cusp_formula {τ : ℍ → ℍ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0)
    (hτ : ∀ᶠ z in atImInfty,
      (τ z : ℂ) = (z : ℂ) / Triangle.width + h (Triangle.cuspQ z)) :
    Tendsto (fun z : ℍ => (τ z).im) atImInfty atTop := by
  have hheight : Tendsto (fun z : ℍ => z.im / Triangle.width) atImInfty atTop :=
    (show Tendsto UpperHalfPlane.im atImInfty atTop from tendsto_comap).atTop_div_const
      Triangle.width_pos
  have hremainder : Tendsto (fun z : ℍ => (h (Triangle.cuspQ z)).im)
      atImInfty (𝓝 (h 0).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp (cusp_analytic_tendsto hh)
  apply (hheight.atTop_add hremainder).congr'
  filter_upwards [hτ] with z hz
  simpa only [Complex.add_im, Complex.div_ofReal_im, UpperHalfPlane.coe_im] using
    (congrArg Complex.im hz).symm

/-- The first period itself therefore tends to the upper-half-plane cusp. -/
theorem tau_tendsto_atImInfty_of_cusp_formula {τ : ℍ → ℍ} {h : ℂ → ℂ}
    (hh : AnalyticAt ℂ h 0)
    (hτ : ∀ᶠ z in atImInfty,
      (τ z : ℂ) = (z : ℂ) / Triangle.width + h (Triangle.cuspQ z)) :
    Tendsto τ atImInfty atImInfty := by
  simpa only [UpperHalfPlane.atImInfty, tendsto_comap_iff, Function.comp_def] using
    tau_im_tendsto_atTop_of_cusp_formula hh hτ

/-- The actual three entries agree with the cusp-period point on a
horodisc, including the sign of the third entry. -/
theorem periodPoint_eventually_eq_cuspPeriodPoint
    {τ : ℍ → ℍ} {μ β : ℍ → ℂ} {m b h : ℂ → ℂ}
    (hτ : ∀ᶠ z in atImInfty,
      (τ z : ℂ) = (z : ℂ) / Triangle.width + h (Triangle.cuspQ z))
    (hμ : ∀ᶠ z in atImInfty, μ z = m (Triangle.cuspQ z))
    (hβ : ∀ᶠ z in atImInfty, β z + (τ z : ℂ) = b (Triangle.cuspQ z)) :
    ∀ᶠ z in atImInfty,
      (⟨(τ z : ℂ), μ z, β z⟩ : PeriodPoint) =
        cuspPeriodPoint m b h ((z : ℂ) / Triangle.width) := by
  filter_upwards [hτ, hμ, hβ] with z hτz hμz hβz
  apply PeriodPoint.ext
  · simpa only [cuspPeriodPoint, exponential_normalized_eq_cuspQ] using hτz
  · simpa only [cuspPeriodPoint, exponential_normalized_eq_cuspQ] using hμz
  · change β z = b (exponential ((z : ℂ) / Triangle.width)) -
      (z : ℂ) / Triangle.width - h (exponential ((z : ℂ) / Triangle.width))
    rw [exponential_normalized_eq_cuspQ]
    calc
      β z = b (Triangle.cuspQ z) - (τ z : ℂ) := eq_sub_of_add_eq hβz
      _ = b (Triangle.cuspQ z) - (z : ℂ) / Triangle.width - h (Triangle.cuspQ z) := by
        rw [hτz]
        ring

/-- The actual left period block is the logarithmic period matrix near
the cusp, with the exact normalization of the original source. -/
theorem leftBlock_eventually_eq_logarithmicPeriod
    {τ : ℍ → ℍ} {μ β : ℍ → ℂ} {m b h : ℂ → ℂ}
    (hτ : ∀ᶠ z in atImInfty,
      (τ z : ℂ) = (z : ℂ) / Triangle.width + h (Triangle.cuspQ z))
    (hμ : ∀ᶠ z in atImInfty, μ z = m (Triangle.cuspQ z))
    (hβ : ∀ᶠ z in atImInfty, β z + (τ z : ℂ) = b (Triangle.cuspQ z)) :
    ∀ᶠ z in atImInfty,
      (⟨(τ z : ℂ), μ z, β z⟩ : PeriodPoint).leftBlock =
        logarithmicPeriod (cuspCorrection m b h) ((z : ℂ) / Triangle.width) := by
  filter_upwards [periodPoint_eventually_eq_cuspPeriodPoint hτ hμ hβ] with z hz
  rw [hz, cuspPeriodPoint_leftBlock]

/-- Every eventual assertion high in the source upper half-plane holds
on the full inverse image of some genuinely small punctured cusp disc. -/
theorem eventual_cuspQ_radius {P : ℍ → Prop} (hP : ∀ᶠ z in atImInfty, P z) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℍ, ‖Triangle.cuspQ z‖ < r → P z := by
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hP
  refine ⟨Real.exp (-2 * Real.pi * Y / Triangle.width), Real.exp_pos _, ?_⟩
  intro z hz
  exact hY z ((Triangle.cuspQ_norm_lt_exp_iff Y z).mp hz).le

/-- A prescribed positive radius can also be respected. -/
theorem eventual_cuspQ_radius_lt {P : ℍ → Prop} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hP : ∀ᶠ z in atImInfty, P z) :
    ∃ r : ℝ, 0 < r ∧ r < r₀ ∧ ∀ z : ℍ, ‖Triangle.cuspQ z‖ < r → P z := by
  obtain ⟨r, hr, h⟩ := eventual_cuspQ_radius hP
  refine ⟨min r (r₀ / 2), lt_min hr (half_pos hr₀),
    (min_le_right _ _).trans_lt (half_lt_self hr₀), ?_⟩
  intro z hz
  exact h z (hz.trans_le (min_le_left _ _))

/-- An additive constant in the third period adds the same constant to
its actual analytic cusp remainder. -/
theorem beta_add_const_cusp_formula {τ : ℍ → ℍ} {β : ℍ → ℂ} {b : ℂ → ℂ}
    (hβ : ∀ᶠ z in atImInfty, β z + (τ z : ℂ) = b (Triangle.cuspQ z)) (c : ℂ) :
    ∀ᶠ z in atImInfty,
      (β z + c) + (τ z : ℂ) = (fun q => b q + c) (Triangle.cuspQ z) := by
  filter_upwards [hβ] with z hz
  simpa only [add_right_comm] using congrArg (fun w : ℂ => w + c) hz

end Wikipedia.HopfProblem.SpecialPeriods.Construction
