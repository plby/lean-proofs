import Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

/-!
# Continuous target-chart perturbations before smoothing

The chart perturbation is valid and jointly continuous even when the original
map is only continuous. Smoothness at any point where the original map is
already smooth is retained. These facts support relative manifold-valued smoothing.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ChartMapPerturbation

variable {E G F H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace N] [ChartedSpace K N]
  (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : X → N} {β : X → ℝ}

theorem continuousAt_coordinateFamily (hf : Continuous f) (hβ : Continuous β)
    (q : F × X) (hq : f q.2 ∈ c.source) :
    ContinuousAt (coordinateFamily c f β) q :=
  ((c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds hq)).comp
    (f := fun r : F × X => f r.2)
    (hf.comp continuous_snd).continuousAt).add
    ((hβ.comp continuous_snd).continuousAt.smul continuousAt_fst)

/-- Compact support supplies a uniform valid parameter neighborhood for a continuous map. -/
theorem eventually_valid_of_continuous (hf : Continuous f) (hβ : Continuous β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) :
    ∀ᶠ a in 𝓝 (0 : F), Valid c f β a := by
  apply hcompact.isCompact.eventually_forall_of_forall_eventually
  intro x hx
  apply (continuousAt_coordinateFamily c hf hβ (0, x) (hsupport hx)).preimage_mem_nhds
  apply c.open_target.mem_nhds
  simpa only [coordinateFamily, smul_zero, add_zero] using c.map_source' (hsupport hx)

theorem exists_radius_valid_of_continuous (hf : Continuous f) (hβ : Continuous β)
    (hcompact : HasCompactSupport β) (hsupport : tsupport β ⊆ f ⁻¹' c.source) :
    ∃ ε > (0 : ℝ), ∀ a : F, ‖a‖ < ε → Valid c f β a := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (eventually_valid_of_continuous c hf hβ hcompact hsupport)
  exact ⟨ε, hε, fun a ha => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ha)⟩

/-- The actual piecewise map is jointly continuous at every valid parameter. -/
theorem continuousAt_perturb (hf : Continuous f) (hβ : Continuous β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : F × X) (ha : Valid c f β q.1) :
    ContinuousAt (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord := continuousAt_coordinateFamily c hf hβ q hx
    have htarget := coordinate_mem_target c f β ha hx
    have hh := (c.contMDiffOn_invFun.continuousOn.continuousAt
      (c.open_target.mem_nhds htarget)).comp hcoord
    apply hh.congr
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.comp continuous_snd).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, if_pos, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp continuous_snd).continuousAt.congr
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact (perturb_eq_of_zero c f β r.1 hr).symm

/-- Compact target-open conditions are stable before any smoothness assumption is made. -/
theorem eventually_maps_compact_into_open_of_continuous (hf : Continuous f) (hβ : Continuous β)
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) {L : Set X} (hL : IsCompact L)
    {U : Set N} (hU : IsOpen U) (hfL : MapsTo f L U) :
    ∀ᶠ a in 𝓝 (0 : F), MapsTo (perturb c f β a) L U := by
  apply hL.eventually_forall_of_forall_eventually
  intro x hx
  apply (continuousAt_perturb c hf hβ hsupport (0, x) (valid_zero c f β hsupport)).preimage_mem_nhds
  apply hU.mem_nhds
  simpa only [perturb_zero] using hfL hx

/-- Pointwise smoothness of the old map is enough for pointwise smoothness of the family. -/
theorem contMDiffAt_perturb_of_contMDiffAt
    (hsupport : tsupport β ⊆ f ⁻¹' c.source) (q : F × X)
    (hf : ContMDiffAt I J ∞ f q.2) (hβ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ β q.2)
    (ha : Valid c f β q.1) :
    ContMDiffAt (𝓘(ℝ, F).prod I) J ∞ (fun r : F × X => perturb c f β r.1 r.2) q := by
  classical
  by_cases hx : f q.2 ∈ c.source
  · have hcoord : ContMDiffAt (𝓘(ℝ, F).prod I) 𝓘(ℝ, F) ∞ (coordinateFamily c f β) q :=
      ((c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx)).comp q
        (hf.comp q contMDiffAt_snd)).add
        ((hβ.comp q contMDiffAt_snd).smul contMDiffAt_fst)
    have htarget := coordinate_mem_target c f β ha hx
    have hh := (c.contMDiffOn_invFun.contMDiffAt (c.open_target.mem_nhds htarget)).comp q hcoord
    apply hh.congr_of_eventuallyEq
    have hs : ∀ᶠ r : F × X in 𝓝 q, f r.2 ∈ c.source :=
      (hf.continuousAt.comp continuousAt_snd).preimage_mem_nhds (c.open_source.mem_nhds hx)
    filter_upwards [hs] with r hr
    simp only [perturb, hr, if_pos, Function.comp_apply]
    rfl
  · have hn : q.2 ∉ tsupport β := fun h => hx (hsupport h)
    have hz : β =ᶠ[𝓝 q.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hn
    apply (hf.comp q contMDiffAt_snd).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hz] with r hr
    exact perturb_eq_of_zero c f β r.1 hr

end Wikipedia.SmoothSixDPoincare.ChartMapPerturbation
