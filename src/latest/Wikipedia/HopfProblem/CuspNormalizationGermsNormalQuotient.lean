import Wikipedia.HopfProblem.CuspNormalizationGermsNormalQuotientCore
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalDirection
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalCylinder
import Wikipedia.HopfProblem.CuspNormalizationGermsNormalIntegral

/-!
# Holomorphic extension of a bounded two-variable analytic quotient

For an actual nonzero analytic denominator germ, choose a transverse
complex line and a zero-free boundary cylinder.  The actual Cauchy
integral on that fixed circle is jointly analytic by the bounded
double-contour construction.  One-variable removable singularities
identify it with the bounded quotient; the analytic identity theorem
gives an equality of actual analytic germs, including on the zero set.

No several-variable removable-singularity or normality theorem is assumed.
-/

noncomputable section

open Set Filter Topology Metric

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

open ToricCharts

/-- Every locally bounded quotient of actual two-variable analytic germs
with nonzero denominator germ has a genuine holomorphic factor. -/
theorem exists_analytic_quotient_of_bounded
    {f g : CoordinateSpace 2 → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hgerm : ¬ g =ᶠ[𝓝 0] 0) {M : ℝ}
    (hbound : ∀ᶠ z in 𝓝 (0 : CoordinateSpace 2), g z ≠ 0 → ‖f z / g z‖ ≤ M) :
    ∃ q : CoordinateSpace 2 → ℂ, AnalyticAt ℂ q 0 ∧
      f =ᶠ[𝓝 0] (fun z => g z * q z) := by
  obtain ⟨e, hline⟩ := NormalDirection.exists_coordinate_change_nonzero_line hg hgerm
  let f' : ℂ × ℂ → ℂ := f ∘ e
  let g' : ℂ × ℂ → ℂ := g ∘ e
  have he : AnalyticAt ℂ (e : ℂ × ℂ → CoordinateSpace 2) 0 :=
    e.toContinuousLinearMap.analyticAt 0
  have hf' : AnalyticAt ℂ f' 0 := hf.comp_of_eq he (map_zero e)
  have hg' : AnalyticAt ℂ g' 0 := hg.comp_of_eq he (map_zero e)
  have heT : Tendsto e (𝓝 (0 : ℂ × ℂ)) (𝓝 (0 : CoordinateSpace 2)) := by
    simpa only [map_zero] using e.continuous.continuousAt.tendsto (x := (0 : ℂ × ℂ))
  have hbound' : ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), g' z ≠ 0 → ‖f' z / g' z‖ ≤ M :=
    heT.eventually hbound
  obtain ⟨r, hr, R, hR, hfc, hgc, hbc, hboundary⟩ :=
    NormalCylinder.exists_bounded_analytic_cylinder hf' hg' hline hbound'
  let q' := NormalIntegral.cauchyQuotient f' g' R
  have hq' : AnalyticAt ℂ q' 0 :=
    NormalIntegral.cauchyQuotient_analyticAt_zero hr hR hfc hgc hboundary
  have hoff' : ∀ᶠ z in 𝓝 (0 : ℂ × ℂ), g' z ≠ 0 → q' z = f' z / g' z := by
    have hU : ball (0 : ℂ) r ×ˢ ball (0 : ℂ) R ∈ 𝓝 (0 : ℂ × ℂ) :=
      (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hr, mem_ball_self hR⟩
    filter_upwards [hU] with z hz
    exact cauchyQuotient_eq_div_of_bounded hfc hgc hbc hboundary hz
  let q : CoordinateSpace 2 → ℂ := q' ∘ e.symm
  have hq : AnalyticAt ℂ q 0 :=
    hq'.comp_of_eq (e.symm.toContinuousLinearMap.analyticAt 0) (map_zero e.symm)
  have heS : Tendsto e.symm (𝓝 (0 : CoordinateSpace 2)) (𝓝 (0 : ℂ × ℂ)) := by
    simpa only [map_zero] using
      e.symm.continuous.continuousAt.tendsto (x := (0 : CoordinateSpace 2))
  have hoff : ∀ᶠ z in 𝓝 (0 : CoordinateSpace 2), g z ≠ 0 → q z = f z / g z := by
    filter_upwards [heS.eventually hoff'] with z hz
    change g' (e.symm z) ≠ 0 → q' (e.symm z) = f' (e.symm z) / g' (e.symm z) at hz
    simpa only [f', g', q, Function.comp_apply, e.apply_symm_apply] using hz
  exact ⟨q, hq, analytic_factorization_of_off_zero hf hg hq hgerm hoff⟩

end Wikipedia.HopfProblem.CuspNormalization.Germs
