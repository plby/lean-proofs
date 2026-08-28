import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationPolydiscAnalyticCoordinates
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Continuous removability of the origin in the affine plane

One-variable continuous removability is applied to every coordinate
slice. The proved joint-analyticity theorem for continuous separately
holomorphic functions then removes the origin in the actual plane.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowdownDescent

open PeriodTorusLineBundleClassificationPolydiscAnalytic

theorem differentiable_of_continuous_of_differentiable_off_zero {h : ℂ → ℂ}
    (hc : Continuous h) (hd : ∀ z ≠ 0, DifferentiableAt ℂ h z) : Differentiable ℂ h := by
  intro z
  by_cases hz : z = 0
  · subst z
    apply (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ hc.continuousAt).differentiableAt
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact hd w hw
  · exact hd z hz

theorem analyticOnNhd_of_continuous_of_differentiable_off_origin {f : ℂ × ℂ → ℂ}
    (hc : Continuous f) (hd : ∀ q ≠ 0, DifferentiableAt ℂ f q) :
    AnalyticOnNhd ℂ f univ := by
  apply analyticOnNhd_of_continuousOn_of_slices isOpen_univ hc.continuousOn
  · intro w
    have hs : Differentiable ℂ (fun v => f (v, w)) := by
      apply differentiable_of_continuous_of_differentiable_off_zero
        (hc.comp (continuous_id.prodMk continuous_const))
      intro v hv
      have hq : (v, w) ≠ (0 : ℂ × ℂ) := fun he => hv (congrArg Prod.fst he)
      exact (hd (v, w) hq).comp v
        (differentiable_id.prodMk (differentiable_const w)).differentiableAt
    exact hs.differentiableOn
  · intro v
    have hs : Differentiable ℂ (fun w => f (v, w)) := by
      apply differentiable_of_continuous_of_differentiable_off_zero
        (hc.comp (continuous_const.prodMk continuous_id))
      intro w hw
      have hq : (v, w) ≠ (0 : ℂ × ℂ) := fun he => hw (congrArg Prod.snd he)
      exact (hd (v, w) hq).comp w
        ((differentiable_const v).prodMk differentiable_id).differentiableAt
    exact hs.differentiableOn

theorem analyticOnNhd_native_of_continuous_of_differentiable_off_origin
    {f : ComplexPlane₂ → ℂ} (hc : Continuous f)
    (hd : ∀ q ≠ 0, DifferentiableAt ℂ f q) : AnalyticOnNhd ℂ f univ := by
  apply analyticOnNhd_complexPlane₂_of_pair
  have ha : AnalyticOnNhd ℂ (f ∘ complexPairEquiv.symm) univ := by
    apply analyticOnNhd_of_continuous_of_differentiable_off_origin
      (hc.comp complexPairEquiv.symm.continuous)
    intro q hq
    have hne : complexPairEquiv.symm q ≠ 0 := by
      intro he
      apply hq
      exact complexPairEquiv.symm.injective (he.trans complexPairEquiv.symm.map_zero.symm)
    exact (hd _ hne).comp q complexPairEquiv.symm.differentiableAt
  simpa only [preimage_univ] using ha

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowdownDescent
