import Wikipedia.SmoothSixDPoincare.SupportedDiffeomorphExtension

/-!
# Joint smoothness of uniformly supported coordinate changes

The compact coordinate support is uniform in the time parameter. The same
support-image argument therefore proves joint smoothness of the actual
extended family across the chart boundary.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E F H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [T2Space Y]
  (Φ : PartialDiffeomorph I J X Y ∞)

/-- A jointly smooth, uniformly supported coordinate family extends jointly smoothly. -/
theorem contMDiff_extendFamily {A : ℝ × X → X}
    (hA : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ A)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ t x, x ∉ K → A (t, x) = x)
    (hsource : ∀ t, MapsTo (fun x => A (t, x)) Φ.source Φ.source) :
    ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞
      (fun p : ℝ × Y => extendMap Φ (fun x => A (p.1, x)) p.2) := by
  intro p
  by_cases hp : p.2 ∈ Φ.target
  · have hback := (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hp)).comp p
      (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, ℝ).prod J) J ∞ Prod.snd p)
    have hpair := contMDiffAt_fst.prodMk hback
    have hchange := hA.contMDiffAt.comp p hpair
    have hforward := Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hsource p.1 (Φ.map_target' hp)))
    apply (hforward.comp p hchange).congr_of_eventuallyEq
    have hn : ∀ᶠ q : ℝ × Y in 𝓝 p, q.2 ∈ Φ.target :=
      continuous_snd.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hp)
    filter_upwards [hn] with q hq
    exact extendMap_of_mem Φ (fun x => A (q.1, x)) hq
  · have hc : IsClosed (Φ '' K) :=
      (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
    have hnot : p.2 ∉ Φ '' K := by
      rintro ⟨x, hx, hxp⟩
      exact hp (hxp ▸ Φ.map_source' (hKΦ hx))
    have hsnd : ContMDiffAt (𝓘(ℝ, ℝ).prod J) J ∞ Prod.snd p := contMDiffAt_snd
    apply hsnd.congr_of_eventuallyEq
    have hn : ∀ᶠ q : ℝ × Y in 𝓝 p, q.2 ∉ Φ '' K :=
      continuous_snd.continuousAt.preimage_mem_nhds (hc.isOpen_compl.mem_nhds hnot)
    filter_upwards [hn] with q hq
    exact extendMap_eq_of_notMem_image Φ (hfix q.1) hq

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Joint smoothness at a parameter only requires source preservation at that parameter.
This allows vector-valued parameter families whose valid parameters form a small open ball. -/
theorem contMDiffAt_extendFamily {A : P × X → X}
    (hA : ContMDiff (𝓘(ℝ, P).prod I) I ∞ A)
    {K : Set X} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ t x, x ∉ K → A (t, x) = x) {p : P × Y}
    (hsource : MapsTo (fun x => A (p.1, x)) Φ.source Φ.source) :
    ContMDiffAt (𝓘(ℝ, P).prod J) J ∞
      (fun q : P × Y => extendMap Φ (fun x => A (q.1, x)) q.2) p := by
  by_cases hp : p.2 ∈ Φ.target
  · have hback := (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hp)).comp p
      (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, P).prod J) J ∞ Prod.snd p)
    have hpair := contMDiffAt_fst.prodMk hback
    have hchange := hA.contMDiffAt.comp p hpair
    have hforward := Φ.contMDiffOn_toFun.contMDiffAt
      (Φ.open_source.mem_nhds (hsource (Φ.map_target' hp)))
    apply (hforward.comp p hchange).congr_of_eventuallyEq
    have hn : ∀ᶠ q : P × Y in 𝓝 p, q.2 ∈ Φ.target :=
      continuous_snd.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hp)
    filter_upwards [hn] with q hq
    exact extendMap_of_mem Φ (fun x => A (q.1, x)) hq
  · have hc : IsClosed (Φ '' K) :=
      (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
    have hnot : p.2 ∉ Φ '' K := by
      rintro ⟨x, hx, hxp⟩
      exact hp (hxp ▸ Φ.map_source' (hKΦ hx))
    have hsnd : ContMDiffAt (𝓘(ℝ, P).prod J) J ∞ Prod.snd p := contMDiffAt_snd
    apply hsnd.congr_of_eventuallyEq
    have hn : ∀ᶠ q : P × Y in 𝓝 p, q.2 ∉ Φ '' K :=
      continuous_snd.continuousAt.preimage_mem_nhds (hc.isOpen_compl.mem_nhds hnot)
    filter_upwards [hn] with q hq
    exact extendMap_eq_of_notMem_image Φ (hfix q.1) hq

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
