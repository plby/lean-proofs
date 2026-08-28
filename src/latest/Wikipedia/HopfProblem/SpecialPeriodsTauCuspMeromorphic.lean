import Wikipedia.HopfProblem.SpecialPeriodsTauCuspPole
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspLift

/-!
# Logarithmic modular lifts from actual meromorphic simple poles

The meromorphic order supplies the analytic numerator. Composing its
factorization with the actual modular cusp inverse gives a lift of the
original meromorphic function, not merely of an assumed coefficient germ.
The normalization of the numerator determines the logarithmic correction
at zero, and the whole cusp lift supplies an actual ambient local germ.
-/

open Filter Set Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

open CuspUniformization

private theorem logarithmic_lift_of_factorization {F a : ℂ → ℂ}
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ≠ 0) {rF : ℝ} (hrF : 0 < rF)
    (hfactor : ∀ t ∈ Metric.ball 0 rF, t ≠ 0 → F t = a t / t)
    {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) :
    ∃ r > 0, r < r₀ ∧ r < 1 ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧ h 0 = logarithm (1 / a 0) ∧
      ∀ s ∈ CuspFamily.logBase r,
        0 < (correctedLogarithm h s).im ∧
        ‖exponential (correctedLogarithm h s)‖ < R ∧
        modularJ (ofComplex (correctedLogarithm h s)) = F (exponential s) := by
  obtain ⟨r, hr, hrr, hr1, h, hh, hh0, _, hlift⟩ :=
    exists_simplePole_logarithmic_lift ha ha0 hR (lt_min hr₀ hrF)
  have hrr₀ : r < r₀ := lt_of_lt_of_le hrr (min_le_left r₀ rF)
  have hrrF : r < rF := lt_of_lt_of_le hrr (min_le_right r₀ rF)
  refine ⟨r, hr, hrr₀, hr1, h, hh, hh0, ?_⟩
  intro s hs
  have hst : exponential s ∈ Metric.ball (0 : ℂ) r := hs
  have hFs := hfactor (exponential s) (Metric.ball_subset_ball hrrF.le hst)
    (exponential_ne_zero s)
  exact ⟨(hlift s hs).2.1, (hlift s hs).2.2.1, (hlift s hs).2.2.2.trans hFs.symm⟩

/-- Every actual meromorphic simple pole has a logarithmic modular lift
on a sufficiently high cusp half-plane. Both radii can be prescribed. -/
theorem exists_meromorphic_simplePole_logarithmic_lift {F : ℂ → ℂ}
    (hF : MeromorphicAt F 0) (horder : meromorphicOrderAt F 0 = (-1 : ℤ))
    {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) :
    ∃ r > 0, r < r₀ ∧ r < 1 ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧
      ∀ s ∈ CuspFamily.logBase r,
        0 < (correctedLogarithm h s).im ∧
        ‖exponential (correctedLogarithm h s)‖ < R ∧
        modularJ (ofComplex (correctedLogarithm h s)) = F (exponential s) := by
  obtain ⟨a, ha, ha0, rF, hrF, hfactor⟩ := simplePole_factorization hF horder
  obtain ⟨r, hr, hrr₀, hr1, h, hh, _, hlift⟩ :=
    logarithmic_lift_of_factorization ha ha0 hrF hfactor hR hr₀
  exact ⟨r, hr, hrr₀, hr1, h, hh, hlift⟩

/-- The punctured leading-coefficient limit fixes the logarithmic
normalization. In particular `c = 1728` gives `h(0) = log(1/1728)/(2πi)`. -/
theorem exists_meromorphic_simplePole_logarithmic_lift_of_tendsto {F : ℂ → ℂ}
    (hF : MeromorphicAt F 0) (horder : meromorphicOrderAt F 0 = (-1 : ℤ)) {c : ℂ}
    (hc : Tendsto (fun t => t * F t) (𝓝[≠] 0) (𝓝 c))
    {R r₀ : ℝ} (hR : 0 < R) (hr₀ : 0 < r₀) :
    ∃ r > 0, r < r₀ ∧ r < 1 ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (Metric.ball 0 r) ∧ h 0 = logarithm (1 / c) ∧
      ∀ s ∈ CuspFamily.logBase r,
        0 < (correctedLogarithm h s).im ∧
        ‖exponential (correctedLogarithm h s)‖ < R ∧
        modularJ (ofComplex (correctedLogarithm h s)) = F (exponential s) := by
  obtain ⟨a, ha, ha0, hac, rF, hrF, hfactor⟩ :=
    simplePole_factorization_of_tendsto hF horder hc
  obtain ⟨r, hr, hrr₀, hr1, h, hh, hh0, hlift⟩ :=
    logarithmic_lift_of_factorization ha ha0 hrF hfactor hR hr₀
  exact ⟨r, hr, hrr₀, hr1, h, hh, by simpa only [hac] using hh0, hlift⟩

/-- The cusp construction supplies a genuine ambient holomorphic modular
lift germ at an actual point of the source upper half-plane. -/
theorem exists_meromorphic_simplePole_ambient_germ {F : ℂ → ℂ}
    (hF : MeromorphicAt F 0) (horder : meromorphicOrderAt F 0 = (-1 : ℤ)) :
    ∃ a : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (a : ℂ) ∧ 0 < (g a).im ∧
      ∀ᶠ z in 𝓝 (a : ℂ), modularJ (ofComplex (g z)) = F (exponential z) := by
  obtain ⟨r, hr, _, hr1, h, hh, hlift⟩ :=
    exists_meromorphic_simplePole_logarithmic_lift hF horder
      (R := 1) (r₀ := 1) zero_lt_one zero_lt_one
  obtain ⟨s, hs⟩ := logBase_set_nonempty r hr
  have hspos : 0 < s.im := upperHalfPlane_of_exponential_norm_lt_one
    (((CuspFamily.mem_logBase r s).mp hs).trans hr1)
  refine ⟨⟨s, hspos⟩, correctedLogarithm h,
    correctedLogarithm_analyticAt hh hs, (hlift s hs).1, ?_⟩
  filter_upwards [(CuspFamily.logBase r).isOpen.mem_nhds hs] with z hz
  exact (hlift z hz).2.2

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
