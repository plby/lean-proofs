import Wikipedia.SmoothSixDPoincare.StripCoordinateBlend
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# A smooth strip map retaining both full corner germs

Construct two smooth time cutoffs supported where the corner center sections
and normal derivatives already agree with the model strip. Blending preserves
both data globally while retaining each entire two-dimensional endpoint germ.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.StripCoordinates

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Construct a globally smooth strip coordinate map with both prescribed full endpoint germs. -/
theorem exists_smooth_strip_matching_germs {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B}
    (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀) (hF₁ : ContDiff ℝ ∞ F₁)
    (hc₀ : (fun t : ℝ => F₀ (t, 0)) =ᶠ[𝓝 0] center)
    (hc₁ : (fun t : ℝ => F₁ (t, 0)) =ᶠ[𝓝 1] center)
    (hn₀ : normalDerivative F₀ =ᶠ[𝓝 (0 : ℝ)] v)
    (hn₁ : normalDerivative F₁ =ᶠ[𝓝 (1 : ℝ)] v) :
    ∃ F : (ℝ × ℝ) → Space A B, ContDiff ℝ ∞ F ∧
      (∀ t, F (t, 0) = center t) ∧ (∀ t, normalDerivative F t = v t) ∧
      (F =ᶠ[𝓝 (0, 0)] F₀) ∧ (F =ᶠ[𝓝 (1, 0)] F₁) := by
  have hgood₀ : {t : ℝ | F₀ (t, 0) = center t ∧ normalDerivative F₀ t = v t ∧ t < 1 / 3}
      ∈ 𝓝 (0 : ℝ) := by
    filter_upwards [hc₀, hn₀, Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t hc hn ht
    exact ⟨hc, hn, ht⟩
  have hgood₁ : {t : ℝ | F₁ (t, 0) = center t ∧ normalDerivative F₁ t = v t ∧ 2 / 3 < t}
      ∈ 𝓝 (1 : ℝ) := by
    filter_upwards [hc₁, hn₁, Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t hc hn ht
    exact ⟨hc, hn, ht⟩
  obtain ⟨β₀, _, hβ₀⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ℝ)) (0 : ℝ)).mem_iff.mp hgood₀
  obtain ⟨β₁, _, hβ₁⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ℝ)) (1 : ℝ)).mem_iff.mp hgood₁
  have hcβ₀ (t : ℝ) (ht : β₀ t ≠ 0) : F₀ (t, 0) = center t :=
    (hβ₀ (subset_tsupport β₀ ht)).1
  have hcβ₁ (t : ℝ) (ht : β₁ t ≠ 0) : F₁ (t, 0) = center t :=
    (hβ₁ (subset_tsupport β₁ ht)).1
  have hnβ₀ (t : ℝ) (ht : β₀ t ≠ 0) : normalDerivative F₀ t = v t :=
    (hβ₀ (subset_tsupport β₀ ht)).2.1
  have hnβ₁ (t : ℝ) (ht : β₁ t ≠ 0) : normalDerivative F₁ t = v t :=
    (hβ₁ (subset_tsupport β₁ ht)).2.1
  have hβ₀zero : (β₀ : ℝ → ℝ) =ᶠ[𝓝 (1 : ℝ)] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro ht
    have hbad : (1 : ℝ) < 1 / 3 := (hβ₀ ht).2.2
    norm_num at hbad
  have hβ₁zero : (β₁ : ℝ → ℝ) =ᶠ[𝓝 (0 : ℝ)] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro ht
    have hbad : (2 / 3 : ℝ) < 0 := (hβ₁ ht).2.2
    norm_num at hbad
  let F := blend v F₀ F₁ β₀ β₁
  have hF : ContDiff ℝ ∞ F :=
    contDiff_blend hv hF₀ hF₁ β₀.contMDiff.contDiff β₁.contMDiff.contDiff
  refine ⟨F, hF, blend_zero hcβ₀ hcβ₁,
    normalDerivative_blend hv hF₀ hF₁ β₀.contMDiff.contDiff β₁.contMDiff.contDiff hnβ₀ hnβ₁,
    ?_, ?_⟩
  · have hp : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_fst.continuousAt.tendsto
    filter_upwards [hp β₀.eventuallyEq_one, hp hβ₁zero] with p hp₀ hp₁
    exact blend_eq_left hp₀ hp₁
  · have hp : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (𝓝 (1, 0)) (𝓝 1) :=
      continuous_fst.continuousAt.tendsto
    filter_upwards [hp hβ₀zero, hp β₁.eventuallyEq_one] with p hp₀ hp₁
    exact blend_eq_right hp₀ hp₁

end Wikipedia.SmoothSixDPoincare.StripCoordinates
