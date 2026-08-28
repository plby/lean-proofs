import Wikipedia.HopfProblem.SpecialPeriodsModularLocalChartsJ
import Wikipedia.HopfProblem.EllipticDiscOrbits

/-!
# Exact local pullbacks of the modular function

These branches solve the prescribed modular equations themselves, not
only the rotation laws.  The cubic chart at `ρ` gives a simple branch over
`1728 s³`; the quadratic chart at `i` gives a double branch over
`1728 (1+s⁴)`.  No global triangle uniformization or global period map is
assumed or asserted here.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods

theorem analytic_chart_inverse_order_one (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) (he : e a = 0)
    (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target) :
    analyticOrderAt (fun z : ℂ => e.symm z - a) 0 = 1 := by
  have ht : (0 : ℂ) ∈ e.target := he ▸ e.map_source ha
  have hia : e.symm 0 = a := by rw [← he, e.left_inv ha]
  have hfi : AnalyticAt ℂ e (e.symm 0) := hia ▸ hf a ha
  have hii := hi 0 ht
  have hc := hfi.differentiableAt.hasDerivAt.comp 0 hii.differentiableAt.hasDerivAt
  have hnear : ∀ᶠ z : ℂ in 𝓝 0, z ∈ e.target := e.open_target.mem_nhds ht
  have heq : (fun z : ℂ => e (e.symm z)) =ᶠ[𝓝 0] id :=
    hnear.mono fun z hz => e.right_inv hz
  have hm : deriv e (e.symm 0) * deriv e.symm 0 = 1 :=
    (hc.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id 0)
  have hne : deriv e.symm 0 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hm
    exact zero_ne_one hm
  simpa only [hia] using hii.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hne

/-- Pulling an analytic inverse chart back by a nonzero scalar times a
positive power gives exactly that vanishing order. -/
theorem analytic_chart_inverse_power_order (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) (he : e a = 0)
    (hf : AnalyticOnNhd ℂ e e.source) (hi : AnalyticOnNhd ℂ e.symm e.target)
    (c : ℂ) (hc : c ≠ 0) (k : ℕ) (hk : 0 < k) :
    analyticOrderAt (fun z : ℂ => e.symm (c * z ^ k) - a) 0 = (k : ℕ∞) := by
  have ht : (0 : ℂ) ∈ e.target := he ▸ e.map_source ha
  have hg : AnalyticAt ℂ (fun z : ℂ => c * z ^ k) 0 := by fun_prop
  have hg0 : c * (0 : ℂ) ^ k = 0 := by simp [hk.ne']
  have hi0 : AnalyticAt ℂ (fun z : ℂ => e.symm z - a) (c * (0 : ℂ) ^ k) := by
    rw [hg0]
    exact (hi 0 ht).sub analyticAt_const
  have horder : analyticOrderAt (fun z : ℂ => c * z ^ k) 0 = (k : ℕ∞) := by
    rw [hg.analyticOrderAt_eq_natCast]
    refine ⟨fun _ => c, analyticAt_const, hc, ?_⟩
    exact Filter.Eventually.of_forall fun z => by simp [mul_comm]
  have hcomp := hi0.analyticOrderAt_comp (g := fun z : ℂ => c * z ^ k) (z₀ := 0) hg
  simpa only [Function.comp_def, hg0, sub_zero,
    analytic_chart_inverse_order_one e ha he hf hi, horder, one_mul] using hcomp

/-- An inverse chart composed with a power has a genuine positive-radius
analytic domain, mapped into the chart's source. -/
theorem exists_disc_inverse_power_branch (e : OpenPartialHomeomorph ℂ ℂ)
    {a : ℂ} (ha : a ∈ e.source) (he : e a = 0)
    (hi : AnalyticOnNhd ℂ e.symm e.target) (c : ℂ) (k : ℕ) (hk : 0 < k) :
    ∃ r : ℝ, 0 < r ∧
      AnalyticOnNhd ℂ (fun z : ℂ => e.symm (c * z ^ k)) (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, c * z ^ k ∈ e.target) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, e.symm (c * z ^ k) ∈ e.source) := by
  have ht : (0 : ℂ) ∈ e.target := he ▸ e.map_source ha
  have hg : ContinuousAt (fun z : ℂ => c * z ^ k) 0 := by fun_prop
  have hV : ∀ᶠ z : ℂ in 𝓝 0, c * z ^ k ∈ e.target := by
    apply hg.preimage_mem_nhds
    simpa [hk.ne'] using e.open_target.mem_nhds ht
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r, hr, ?_, fun z hz => hball hz, fun z hz => e.map_target (hball hz)⟩
  intro z hz
  exact (hi _ (hball hz)).comp (f := fun w : ℂ => c * w ^ k) (by fun_prop)

/-- The actual local branch at `ρ` solving the normalized cubic modular
equation, with exact simple vanishing. -/
theorem exists_modularJ_cubic_pullback_local :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (Metric.ball 0 r) ∧ τ 0 = rho ∧
      MapsTo τ (Metric.ball 0 r) upperHalfPlaneSet ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r, modularJ (ofComplex (τ s)) = 1728 * s ^ 3) ∧
      analyticOrderAt (fun s => τ s - rho) 0 = 1 := by
  obtain ⟨e, ha, he, hU, hf, hi, _, hp⟩ := modularJ_rhoPoint_cubic_chart
  obtain ⟨r, hr, hτ, ht, hs⟩ := exists_disc_inverse_power_branch e ha he hi 12 1 (by decide)
  refine ⟨r, hr, fun s => e.symm (12 * s ^ 1), hτ, ?_,
    fun s hsr => hU (hs s hsr), ?_, ?_⟩
  · simpa only [zero_pow one_ne_zero, mul_zero, he] using e.left_inv ha
  · intro s hsr
    rw [hp _ (ht s hsr)]
    ring
  · simpa using analytic_chart_inverse_power_order e ha he hf hi 12 (by norm_num) 1
      (by decide)

/-- The actual local branch at `i` solving the quartic pullback of the
quadratic modular equation, with exact double vanishing. -/
theorem exists_modularJ_quartic_pullback_local :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (Metric.ball 0 r) ∧ τ 0 = Complex.I ∧
      MapsTo τ (Metric.ball 0 r) upperHalfPlaneSet ∧
      (∀ s ∈ Metric.ball (0 : ℂ) r,
        modularJ (ofComplex (τ s)) = 1728 * (1 + s ^ 4)) ∧
      analyticOrderAt (fun s => τ s - Complex.I) 0 = 2 := by
  obtain ⟨e, ha, he, hU, hf, hi, _, hp⟩ := modularJ_I_quadratic_chart
  let c : ℂ := 24 * (Real.sqrt 3 : ℂ)
  have hc : c ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3)
  have hc2 : c ^ 2 = 1728 := by
    dsimp [c]
    rw [mul_pow, ← Complex.ofReal_pow]
    norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  obtain ⟨r, hr, hτ, ht, hs⟩ := exists_disc_inverse_power_branch e ha he hi c 2 (by decide)
  refine ⟨r, hr, fun s => e.symm (c * s ^ 2), hτ, ?_,
    fun s hsr => hU (hs s hsr), ?_, ?_⟩
  · simpa only [zero_pow two_ne_zero, mul_zero, he] using e.left_inv ha
  · intro s hsr
    have hh := hp _ (ht s hsr)
    rw [mul_pow, hc2] at hh
    linear_combination hh
  · exact analytic_chart_inverse_power_order e ha he hf hi c hc 2 (by decide)

end Wikipedia.HopfProblem.SpecialPeriods
