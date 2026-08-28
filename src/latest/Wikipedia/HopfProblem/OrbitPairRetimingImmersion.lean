import Wikipedia.HopfProblem.OrbitPairSourceRetiming
import Wikipedia.HopfProblem.OrbitPairTrackNormalDerivative

/-!
# Immersion control for nonuniform source time changes

If the full old three-dimensional family map is immersive in a retiming
corridor, any source diffeomorphism retains immersion there, including on
the new fixed-time slices. Outside that corridor, an unchanged source germ
retains the original spatial derivative. A common translation germ also
retains the old spatial derivative at its translated time.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open Wikipedia.SmoothSixDPoincare

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace K N]
  {F : ℝ × M → N}
  (Ψ : Diffeomorph (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (ℝ × M) (ℝ × M) ∞)

theorem retimed_injective_full_derivative
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F) (p : ℝ × M)
    (hi : Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F (Ψ p))) :
    Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J (retimedFamily F Ψ) p) := by
  let A : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (Ψ p)
  let B : ℝ × E →L[ℝ] ℝ × E :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) Ψ p
  let D : ℝ × E →L[ℝ] G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) J (retimedFamily F Ψ) p
  have hD : D = A.comp B :=
    mfderiv_comp p (hF.mdifferentiableAt (by simp)) (Ψ.contMDiff.mdifferentiableAt (by simp))
  have hB : Bijective B := PartialChart.bijective_mfderiv Ψ.toPartialDiffeomorph (mem_univ p)
  change Injective D
  rw [hD]
  exact hi.comp hB.injective

theorem retimed_injective_spatial_of_full_derivative
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F) (p : ℝ × M)
    (hi : Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F (Ψ p))) :
    Injective (mfderiv I J (fun x => retimedFamily F Ψ (p.1, x)) p.2) := by
  let A : ℝ × E →L[ℝ] G := mfderiv (𝓘(ℝ, ℝ).prod I) J F (Ψ p)
  let B : ℝ × E →L[ℝ] ℝ × E :=
    mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) Ψ p
  let D : ℝ × E →L[ℝ] G :=
    mfderiv (𝓘(ℝ, ℝ).prod I) J (retimedFamily F Ψ) p
  let S : E →L[ℝ] G := mfderiv I J (fun x => retimedFamily F Ψ (p.1, x)) p.2
  have hD : D = A.comp B :=
    mfderiv_comp p (hF.mdifferentiableAt (by simp)) (Ψ.contMDiff.mdifferentiableAt (by simp))
  have hB : Bijective B := PartialChart.bijective_mfderiv Ψ.toPartialDiffeomorph (mem_univ p)
  have hS : S = D.comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    mfderiv_spatial_eq p ((retimedFamily_smooth hF Ψ).mdifferentiableAt (by simp))
  have hinr : Injective (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro u v huv
    exact congrArg Prod.snd huv
  change Injective S
  rw [hS, hD]
  exact (hi.comp hB.injective).comp hinr

theorem retimed_spatial_derivative_of_translation_germ (p : ℝ × M) (c : ℝ)
    (hΨ : Ψ =ᶠ[𝓝 p] fun q => (q.1 + c, q.2)) :
    (mfderiv I J (fun x => retimedFamily F Ψ (p.1, x)) p.2 : E →L[ℝ] G) =
      (mfderiv I J (fun x => F (p.1 + c, x)) p.2 : E →L[ℝ] G) := by
  have hc : ContinuousAt (fun x : M => (p.1, x)) p.2 :=
    continuous_const.continuousAt.prodMk continuous_id.continuousAt
  have he : (fun x => retimedFamily F Ψ (p.1, x)) =ᶠ[𝓝 p.2]
      (fun x => F (p.1 + c, x)) := by
    filter_upwards [hΨ.comp_tendsto hc] with x hx
    exact congrArg F hx
  exact he.mfderiv_eq

theorem retimed_spatial_derivative_of_identity_germ (p : ℝ × M)
    (hΨ : Ψ =ᶠ[𝓝 p] id) :
    (mfderiv I J (fun x => retimedFamily F Ψ (p.1, x)) p.2 : E →L[ℝ] G) =
      (mfderiv I J (fun x => F (p.1, x)) p.2 : E →L[ℝ] G) := by
  have hc : ContinuousAt (fun x : M => (p.1, x)) p.2 :=
    continuous_const.continuousAt.prodMk continuous_id.continuousAt
  have he : (fun x => retimedFamily F Ψ (p.1, x)) =ᶠ[𝓝 p.2]
      (fun x => F (p.1, x)) := by
    filter_upwards [hΨ.comp_tendsto hc] with x hx
    exact congrArg F hx
  exact he.mfderiv_eq

theorem retimed_immersive_of_corridor
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    {S W : Set (ℝ × M)} (hmap : MapsTo Ψ S W)
    (hfull : ∀ p ∈ W, Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F p))
    (hfix : ∀ p ∉ S, Ψ =ᶠ[𝓝 p] id) :
    ∀ t x, Injective (mfderiv I J (fun y => retimedFamily F Ψ (t, y)) x) := by
  intro t x
  by_cases hp : (t, x) ∈ S
  · exact retimed_injective_spatial_of_full_derivative Ψ hF (t, x) (hfull _ (hmap hp))
  · have he := retimed_spatial_derivative_of_identity_germ
      (F := F) (J := J) Ψ (t, x) (hfix _ hp)
    rw [he]
    exact hi t x

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
