import Wikipedia.HopfProblem.DegreeCollapseIsolatedPatchImages
import Wikipedia.HopfProblem.DegreeCollapseSelectiveIntersectionControl
import Wikipedia.HopfProblem.DegreeCollapseSelectiveSupport
import Wikipedia.SmoothSixDPoincare.CompatibleChartCancellation

/-!
# Actual source-selective cancellation in the isolated Whitney chart

The compactly supported ambient motion is constructed from the compatible
chart. Local branch isolation identifies the full unselected source image
with the second branch there. The endpoint motion removes exactly the two
chosen crossing values from the cross-side image intersection and fixes
every retained crossing. Applying it only to the selected source patch
gives a genuine smooth immersed endpoint with exact source-pair control.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet

open Wikipedia.SmoothSixDPoincare WhitneyPairModel

variable {E M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  [TopologicalSpace N] {F : C(N, M)} {U V : Set N}
  {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) (F '' closure U) (F '' closure V) a k₀ k₁}
  {l : CleanStripPatch (E := E) (F '' closure V) (F '' closure U) b l₀ l₁}
  {tube : TubularBigon (E := E) (F '' closure U) (F '' closure V) a b k.map l.map h}
  (c : TubularBigon.CompatibleChart tube)

theorem exists_isolated_patch_cancellation
    (hUV : Disjoint (closure U) (closure V)) (hpre : F ⁻¹' c.chart.target ⊆ U ∪ V) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ c.chart.target ∧ ∃ A : ℝ × M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
      (∀ y, A (0, y) = y) ∧
      (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = d y) ∧
      (∀ t y, y ∉ K → A (t, y) = y) ∧
      ((fun y => A (1, y)) '' (F '' U)) ∩ (F '' Uᶜ) =
        ((F '' U) ∩ (F '' Uᶜ)) \ {a 0, a 1} ∧
      ∀ t y, y ∈ ((F '' U) ∩ (F '' Uᶜ)) \ {a 0, a 1} → A (t, y) = y := by
  obtain ⟨K, hK, hKtarget, A, hA, hzero, hdiff, hfix, hdisjoint⟩ :=
    exists_supported_native_bigon_cancellation c.chart tube.height_pos
      (fun _ hp => c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩)
  obtain ⟨h₁, h₂⟩ := isolated_patch_images subset_closure subset_closure hUV hpre
  rw [c.nativeFirstSheet_eq, c.nativeSecondSheet_eq, ← h₁, ← h₂] at hdisjoint
  have hcross : ((F '' U) ∩ (F '' Uᶜ)) ∩ c.chart.target = {a 0, a 1} :=
    (isolated_cross_intersection subset_closure subset_closure hUV hpre).trans
      c.intersection_in_target_eq
  have hout : ∀ y ∈ ((F '' U) ∩ (F '' Uᶜ)) \ {a 0, a 1}, y ∉ c.chart.target := by
    intro y hy hyO
    apply hy.2
    rw [← hcross]
    exact ⟨hy.1, hyO⟩
  obtain ⟨D, hD⟩ := hdiff 1
  have hDfix : ∀ y ∉ c.chart.target, D y = y :=
    fun y hy => (hD y).symm.trans (hfix 1 y (fun hyK => hy (hKtarget hyK)))
  have hDeq : (fun y => A (1, y)) = D := funext hD
  have hdisjD : Disjoint (D '' ((F '' U) ∩ c.chart.target)) ((F '' Uᶜ) ∩ c.chart.target) := by
    rwa [hDeq] at hdisjoint
  have hinter := SupportedDiffeomorph.image_inter_eq_diff D.toEquiv hDfix hdisjD
  change (D '' (F '' U)) ∩ (F '' Uᶜ) =
    ((F '' U) ∩ (F '' Uᶜ)) \ c.chart.target at hinter
  refine ⟨K, hK, hKtarget, A, hA, hzero, hdiff, hfix, ?_, ?_⟩
  · rw [hDeq, hinter, ← hcross]
    ext y
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  · intro t y hy
    exact hfix t y (fun hyK => hout y hy (hKtarget hyK))

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [ChartedSpace G N] [T2Space N]

theorem exists_immersed_selective_cancellation
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    (hU : IsOpen U) (hV : IsOpen V) (hUc : IsCompact (closure U))
    (hUV : Disjoint (closure U) (closure V)) (hpre : F ⁻¹' c.chart.target ⊆ U ∪ V) :
    ∃ L : Set N, IsCompact L ∧ L ⊆ U ∧ MapsTo F L c.chart.target ∧ ∃ g : C(N, M),
      ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ g ∧ F.Homotopic g ∧
      (∀ x, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) g x)) ∧ (∀ x ∉ L, g x = F x) ∧
      {p : N × N | p.1 ≠ p.2 ∧ g p.1 = g p.2} =
        {p : N × N | p.1 ≠ p.2 ∧ F p.1 = F p.2} \
          {p : N × N | F p.1 ∈ ({a 0, a 1} : Set M) ∧ ¬ (p.1 ∈ U ↔ p.2 ∈ U)} := by
  obtain ⟨K, hK, hKtarget, A, hA, hzero, hdiff, hfix, hinter, hretained⟩ :=
    exists_isolated_patch_cancellation c hUV hpre
  have hpreK : F ⁻¹' K ⊆ U ∪ V := fun _ hx => hpre (hKtarget hx)
  let L : Set N := closure U ∩ F ⁻¹' K
  obtain ⟨hL, hLU⟩ := selected_support_isCompact F.continuous hUc hV
    (hUV.mono subset_closure subset_closure) hK hpreK
  obtain ⟨g, hg, hrel, hi', hgend, hgfix⟩ :=
    exists_immersed_endpoint_homotopic F hU hL.isClosed hLU hF hi hA hzero hdiff
      (fun t x hx hxL => hfix t (F x) (fun hxK => hxL ⟨subset_closure hx, hxK⟩))
  obtain ⟨D, hD⟩ := hdiff 1
  have hAinj : Injective (fun y => A (1, y)) := by
    have he : (fun y => A (1, y)) = D := funext hD
    rw [he]
    exact D.injective
  refine ⟨L, hL, hLU, fun _ hx => hKtarget hx.2, g, hg, hrel, hi', hgfix, ?_⟩
  have hpairs := family_ordered_pairs_eq hAinj hinter (hretained 1)
  have hgeq : (g : N → M) = fun x => family F A U (1, x) := funext hgend
  rw [hgeq]
  exact hpairs

end Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet
