import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticOpen
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Locally uniform limits in two complex variables

Local uniform convergence restricts along each actual coordinate slice.
The one-variable Weierstrass theorem supplies holomorphic limit slices,
and local uniform convergence supplies joint continuity of the limit.
The proved two-variable Cauchy theorem then gives joint analyticity.
The index set and its nontrivial convergence filter are arbitrary.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic

/-- A locally uniform limit on an open subset of `ℂ × ℂ` of eventually
jointly analytic functions is genuinely jointly analytic. -/
theorem analyticOnNhd_of_tendstoLocallyUniformlyOn
    {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ × ℂ → ℂ} {f : ℂ × ℂ → ℂ} {s : Set (ℂ × ℂ)}
    (hs : IsOpen s) (hlim : TendstoLocallyUniformlyOn F f φ s)
    (hF : ∀ᶠ i in φ, AnalyticOnNhd ℂ (F i) s) : AnalyticOnNhd ℂ f s := by
  apply analyticOnNhd_of_continuousOn_of_slices hs
  · exact hlim.continuousOn (hF.mono fun _ hi => hi.continuousOn).frequently
  · intro w
    have hc : Continuous (fun v : ℂ => (v, w)) :=
      continuous_id.prodMk continuous_const
    have hl : TendstoLocallyUniformlyOn (fun i v => F i (v, w))
        (fun v => f (v, w)) φ ((fun v : ℂ => (v, w)) ⁻¹' s) :=
      hlim.comp (fun v => (v, w)) (fun _ hv => hv) hc.continuousOn
    apply hl.differentiableOn ?_ (hs.preimage hc)
    filter_upwards [hF] with i hi
    exact hi.differentiableOn.comp
      (differentiable_id.prodMk (differentiable_const w)).differentiableOn (fun _ hv => hv)
  · intro v
    have hc : Continuous (fun w : ℂ => (v, w)) :=
      continuous_const.prodMk continuous_id
    have hl : TendstoLocallyUniformlyOn (fun i w => F i (v, w))
        (fun w => f (v, w)) φ ((fun w : ℂ => (v, w)) ⁻¹' s) :=
      hlim.comp (fun w => (v, w)) (fun _ hw => hw) hc.continuousOn
    apply hl.differentiableOn ?_ (hs.preimage hc)
    filter_upwards [hF] with i hi
    exact hi.differentiableOn.comp
      ((differentiable_const v).prodMk differentiable_id).differentiableOn (fun _ hw => hw)

/-- Complex differentiability, rather than a supplied analytic expansion,
also suffices for the approximating functions. -/
theorem analyticOnNhd_of_tendstoLocallyUniformlyOn_of_differentiableOn
    {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ × ℂ → ℂ} {f : ℂ × ℂ → ℂ} {s : Set (ℂ × ℂ)}
    (hs : IsOpen s) (hlim : TendstoLocallyUniformlyOn F f φ s)
    (hF : ∀ᶠ i in φ, DifferentiableOn ℂ (F i) s) : AnalyticOnNhd ℂ f s :=
  analyticOnNhd_of_tendstoLocallyUniformlyOn hs hlim
    (hF.mono fun _ hi => analyticOnNhd_of_differentiableOn hs hi)

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic
