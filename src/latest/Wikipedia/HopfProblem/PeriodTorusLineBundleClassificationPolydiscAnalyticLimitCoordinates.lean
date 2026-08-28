import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticCoordinates
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticLimit

/-! # Locally uniform analytic limits on the actual covering space -/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic

/-- The local-uniform limit theorem holds on the original `ComplexPlane₂`,
with its original norm and topology. -/
theorem analyticOnNhd_complexPlane₂_of_tendstoLocallyUniformlyOn
    {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ComplexPlane₂ → ℂ} {f : ComplexPlane₂ → ℂ} {s : Set ComplexPlane₂}
    (hs : IsOpen s) (hlim : TendstoLocallyUniformlyOn F f φ s)
    (hF : ∀ᶠ i in φ, AnalyticOnNhd ℂ (F i) s) : AnalyticOnNhd ℂ f s := by
  apply analyticOnNhd_complexPlane₂_of_pair
  apply analyticOnNhd_of_tendstoLocallyUniformlyOn
    (hs.preimage complexPairEquiv.symm.continuous)
    (hlim.comp complexPairEquiv.symm (fun _ h => h)
      complexPairEquiv.symm.continuous.continuousOn)
  filter_upwards [hF] with i hi
  intro z hz
  exact (hi (complexPairEquiv.symm z) hz).comp
    (complexPairEquiv.symm.toContinuousLinearMap.analyticAt z)

theorem analyticOnNhd_complexPlane₂_of_tendstoLocallyUniformlyOn_of_differentiableOn
    {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ComplexPlane₂ → ℂ} {f : ComplexPlane₂ → ℂ} {s : Set ComplexPlane₂}
    (hs : IsOpen s) (hlim : TendstoLocallyUniformlyOn F f φ s)
    (hF : ∀ᶠ i in φ, DifferentiableOn ℂ (F i) s) : AnalyticOnNhd ℂ f s :=
  analyticOnNhd_complexPlane₂_of_tendstoLocallyUniformlyOn hs hlim
    (hF.mono fun _ hi => analyticOnNhd_complexPlane₂_of_differentiableOn hs hi)

/-- In particular, the limit has the actual `ω` regularity used by native
holomorphic sections and bundle maps. -/
theorem contDiffOn_complexPlane₂_of_tendstoLocallyUniformlyOn_of_differentiableOn
    {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ComplexPlane₂ → ℂ} {f : ComplexPlane₂ → ℂ} {s : Set ComplexPlane₂}
    (hs : IsOpen s) (hlim : TendstoLocallyUniformlyOn F f φ s)
    (hF : ∀ᶠ i in φ, DifferentiableOn ℂ (F i) s) : ContDiffOn ℂ ω f s :=
  (analyticOnNhd_complexPlane₂_of_tendstoLocallyUniformlyOn_of_differentiableOn
    hs hlim hF).contDiffOn_of_completeSpace

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalytic
