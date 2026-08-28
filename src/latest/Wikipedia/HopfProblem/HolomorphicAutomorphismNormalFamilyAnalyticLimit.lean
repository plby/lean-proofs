import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyAnalyticCoordinates
import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyLimit

/-!
# Analytic limits on the native threefold model

The multivariable Weierstrass theorem gives complex differentiability of a
locally uniform limit.  The native three-variable analytic theorem upgrades
this to the actual `ω` regularity used by the manifold charts.  The family is
only required to be eventually differentiable, along any nontrivial filter.
-/

noncomputable section

open Set Filter
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold

variable {ι : Type*} {φ : Filter ι} [φ.NeBot] {s : Set (ℂ × ComplexPlane₂)}

/-- Scalar locally uniform limits are genuinely analytic on the native model. -/
theorem analyticOnNhd_nativeScalar_of_tendstoLocallyUniformlyOn
    {seq : ι → (ℂ × ComplexPlane₂) → ℂ} {f : (ℂ × ComplexPlane₂) → ℂ}
    (hs : IsOpen s) (hlim : TendstoLocallyUniformlyOn seq f φ s)
    (hseq : ∀ᶠ i in φ, DifferentiableOn ℂ (seq i) s) : AnalyticOnNhd ℂ f s :=
  analyticOnNhd_nativeScalar_of_differentiableOn hs
    (tendstoLocallyUniformlyOn_differentiableOn hlim hseq hs)

theorem contDiffOn_nativeScalar_of_tendstoLocallyUniformlyOn
    {seq : ι → (ℂ × ComplexPlane₂) → ℂ} {f : (ℂ × ComplexPlane₂) → ℂ}
    (hs : IsOpen s) (hlim : TendstoLocallyUniformlyOn seq f φ s)
    (hseq : ∀ᶠ i in φ, DifferentiableOn ℂ (seq i) s) : ContDiffOn ℂ ω f s :=
  (analyticOnNhd_nativeScalar_of_tendstoLocallyUniformlyOn hs hlim hseq).contDiffOn_of_completeSpace

/-- Native-model-valued locally uniform limits have actual `C^ω` regularity.
In particular this applies to limits of local automorphism coordinate maps. -/
theorem contDiffOn_nativeModel_of_tendstoLocallyUniformlyOn
    {seq : ι → (ℂ × ComplexPlane₂) → (ℂ × ComplexPlane₂)}
    {f : (ℂ × ComplexPlane₂) → (ℂ × ComplexPlane₂)}
    (hs : IsOpen s) (hlim : TendstoLocallyUniformlyOn seq f φ s)
    (hseq : ∀ᶠ i in φ, DifferentiableOn ℂ (seq i) s) : ContDiffOn ℂ ω f s :=
  contDiffOn_nativeModel_of_differentiableOn hs
    (tendstoLocallyUniformlyOn_differentiableOn hlim hseq hs)

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily.AnalyticThreefold
