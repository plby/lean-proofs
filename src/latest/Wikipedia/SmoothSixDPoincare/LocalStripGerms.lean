import Wikipedia.SmoothSixDPoincare.StripGermBlend
import Wikipedia.SmoothSixDPoincare.CleanStripNeighborhood
import Wikipedia.SmoothSixDPoincare.NonzeroVectorCurveGerms

/-!
# Clean embedded coordinate strips with prescribed local corner germs

Extend the two locally smooth planar germs, construct a nonzero normal field
matching their derivatives, and blend with the model strip. The resulting
actual map has a positive-width clean embedded immersive neighborhood and
agrees with both entire prescribed planar germs.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.StripCoordinates

section General

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem contDiff_normalDerivative {F : (ℝ × ℝ) → Space A B} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (normalDerivative F) :=
  ((hF.snd.fderiv_right (by simp)).clm_apply contDiff_const).comp
    (contDiff_id.prodMk contDiff_const)

omit [NormedAddCommGroup A] [NormedSpace ℝ A] in
theorem normalDerivative_congr_germ {F G : (ℝ × ℝ) → Space A B} {t : ℝ}
    (heq : F =ᶠ[𝓝 (t, 0)] G) : normalDerivative F t = normalDerivative G t := by
  have heq' : (fun p => (F p).2) =ᶠ[𝓝 (t, (0 : ℝ))] (fun p => (G p).2) := by
    filter_upwards [heq] with p hp
    exact congrArg Prod.snd hp
  have hd : fderiv ℝ (fun p => (F p).2) (t, 0) =
      fderiv ℝ (fun p => (G p).2) (t, 0) := heq'.fderiv_eq
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] B => L (0, 1)) hd

end General

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]

/-- Construct a clean positive-width strip retaining both complete locally smooth corner germs. -/
theorem exists_clean_strip_matching_local_germs
    {F₀ F₁ : (ℝ × ℝ) → Space A B} {U₀ U₁ : Set (ℝ × ℝ)}
    (hF₀ : ContDiffOn ℝ ∞ F₀ U₀) (hF₁ : ContDiffOn ℝ ∞ F₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (h0U₀ : (0, 0) ∈ U₀) (h1U₁ : (1, 0) ∈ U₁)
    (hc₀ : (fun t : ℝ => F₀ (t, 0)) =ᶠ[𝓝 0] center)
    (hc₁ : (fun t : ℝ => F₁ (t, 0)) =ᶠ[𝓝 1] center)
    (hn₀ : normalDerivative F₀ 0 ≠ 0) (hn₁ : normalDerivative F₁ 1 ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B)
    {O : Set (Space A B)} (hO : IsOpen O) (hcenterO : MapsTo center (Icc (0 : ℝ) 1) O) :
    ∃ F : (ℝ × ℝ) → Space A B, ContDiff ℝ ∞ F ∧ (∀ t, F (t, 0) = center t) ∧
      (F =ᶠ[𝓝 (0, 0)] F₀) ∧ (F =ᶠ[𝓝 (1, 0)] F₁) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set (ℝ × ℝ), IsOpen W ∧
        Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε ⊆ W ∧ InjOn F W ∧ MapsTo F W O ∧
        (∀ p ∈ W, Injective (fderiv ℝ F p)) ∧
        (∀ p ∈ W, (F p).2 = 0 ↔ p.2 = 0) ∧
        IsClosedEmbedding (fun p : Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε => F p) ∧
        (∀ t, normalDerivative F t ≠ 0) := by
  obtain ⟨G₀, hG₀, heq₀⟩ := exists_smooth_extension_near_point hF₀.contMDiffOn hU₀ h0U₀
  obtain ⟨G₁, hG₁, heq₁⟩ := exists_smooth_extension_near_point hF₁.contMDiffOn hU₁ h1U₁
  have hnG₀ : normalDerivative G₀ 0 ≠ 0 := by rwa [normalDerivative_congr_germ heq₀]
  have hnG₁ : normalDerivative G₁ 1 ≠ 0 := by rwa [normalDerivative_congr_germ heq₁]
  obtain ⟨v, hv, hvne, hv₀, hv₁⟩ := DiskFraming.exists_nonzero_smooth_curve_with_endpoint_germs
    (contDiff_normalDerivative hG₀.contDiff).contDiffOn
    (contDiff_normalDerivative hG₁.contDiff).contDiffOn
    isOpen_univ isOpen_univ (mem_univ _) (mem_univ _) hnG₀ hnG₁ hdim
  have hcG₀ : (fun t : ℝ => G₀ (t, 0)) =ᶠ[𝓝 0] center := by
    have hi : Tendsto (fun t : ℝ => (t, (0 : ℝ))) (𝓝 0) (𝓝 (0, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    exact (heq₀.comp_tendsto hi).trans hc₀
  have hcG₁ : (fun t : ℝ => G₁ (t, 0)) =ᶠ[𝓝 1] center := by
    have hi : Tendsto (fun t : ℝ => (t, (0 : ℝ))) (𝓝 1) (𝓝 (1, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    exact (heq₁.comp_tendsto hi).trans hc₁
  obtain ⟨F, hF, hc, hD, hFG₀, hFG₁⟩ :=
    exists_smooth_strip_matching_germs hv hG₀.contDiff hG₁.contDiff hcG₀ hcG₁ hv₀.symm hv₁.symm
  obtain ⟨ε, hε, W, hW, hrect, hinj, hmap, hi, hclean, hemb⟩ :=
    exists_clean_strip_neighborhood hv hF hc hD (fun t _ => hvne t) hO hcenterO
  exact ⟨F, hF, hc, hFG₀.trans heq₀, hFG₁.trans heq₁,
    ε, hε, W, hW, hrect, hinj, hmap, hi, hclean, hemb,
    fun t => by rw [hD t]; exact hvne t⟩

end Wikipedia.SmoothSixDPoincare.StripCoordinates
