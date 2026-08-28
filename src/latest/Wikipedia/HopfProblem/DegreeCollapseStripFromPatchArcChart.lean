import Wikipedia.SmoothSixDPoincare.NativeStripGerms
import Wikipedia.SmoothSixDPoincare.CornerStripData
import Wikipedia.SmoothSixDPoincare.StripEndpointObstacle
import Wikipedia.SmoothSixDPoincare.StripNormalData

/-!
# A full clean strip from the native patch chart and shared corners

The whole corner germs are retained. A compact shrink excludes additional
contacts with the other closed sheet, while the actual normal coordinate
retains its nonzero transverse derivative along the entire center arc.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare

variable {A B E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]

theorem exists_strip_from_patch_arc_chart
    (Φ : PartialDiffeomorph 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E)
      (StripCoordinates.Space A B) M ∞)
    {S T : Set M} {α a₀ b₀ a₁ b₁ : ℝ → M}
    (hline : MapsTo StripCoordinates.center (Icc (0 : ℝ) 1) Φ.source)
    (hzero : ∀ t, StripCoordinates.center t ∈ Φ.source → Φ (StripCoordinates.center t) = α t)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ S ↔ q.2 = 0)
    (hT : IsClosed T) (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, α t ∉ T)
    (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁)
    (haxis₀ : (fun t : ℝ => c₀.map (t, 0)) =ᶠ[𝓝 0] α)
    (haxis₁ : (fun t : ℝ => c₁.map (t, 0)) =ᶠ[𝓝 0] fun t => α (1-t))
    (hn₀ : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ c₀.map) (0, 0) (0, 1) ≠ 0)
    (hn₁ : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ c₁.map) (0, 0) (0, 1) ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) :
    ∃ k : CleanStripPatch (E := E) S T α c₀.map c₁.map,
      Nonempty (StripNormalData A B (E := E) S k.map) ∧ MapsTo k.map k.domain Φ.target := by
  have hline₀ := hline (by simp : (0 : ℝ) ∈ Icc 0 1)
  have hline₁ := hline (by simp : (1 : ℝ) ∈ Icc 0 1)
  let k₁ := c₁.map ∘ StripCoordinates.reverse
  let U₁ := StripCoordinates.reverse ⁻¹' c₁.domain
  have hU₁ : IsOpen U₁ := c₁.open_domain.preimage StripCoordinates.contDiff_reverse.continuous
  have h1U₁ : (1, 0) ∈ U₁ := by
    change StripCoordinates.reverse (1, 0) ∈ c₁.domain
    rw [StripCoordinates.reverse_one_zero]
    exact c₁.contains_zero
  have hk₁ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁ U₁ :=
    c₁.smooth.comp StripCoordinates.contDiff_reverse.contMDiff.contMDiffOn (fun _ hp => hp)
  have hk₁zero : c₁.map (0, 0) = α 1 := by
    simpa only [sub_zero] using haxis₁.eq_of_nhds
  have hk₁Phi : c₁.map (0, 0) ∈ Φ.target := by
    rw [hk₁zero, ← hzero 1 hline₁]
    exact Φ.map_source' hline₁
  have hnormal := (TransverseCoordinates.contMDiffOn_normalCoordinate Φ).contMDiffAt
    (Φ.open_target.mem_nhds hk₁Phi)
  have hH₁ : DifferentiableAt ℝ (TransverseCoordinates.normalCoordinate Φ ∘ c₁.map) (0, 0) :=
    (hnormal.comp (0, 0) (c₁.smooth.contMDiffAt
      (c₁.open_domain.mem_nhds c₁.contains_zero))).contDiffAt.differentiableAt (by simp)
  have hn₁' : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁) (1, 0) (0, 1) ≠ 0 := by
    change fderiv ℝ ((TransverseCoordinates.normalCoordinate Φ ∘ c₁.map) ∘
      StripCoordinates.reverse) (1, 0) (0, 1) ≠ 0
    rw [StripCoordinates.vertical_derivative_reverse hH₁]
    exact hn₁
  have hcenter : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hmatch₀ : (fun t : ℝ => c₀.map (t, 0)) =ᶠ[𝓝 0]
      fun t => Φ (StripCoordinates.center t) := by
    have hsource := hcenter.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₀)
    filter_upwards [hsource, haxis₀] with t hs he
    exact he.trans (hzero t hs).symm
  have hrev : Tendsto (fun t : ℝ => 1-t) (𝓝 1) (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => 1-t) (𝓝 1) (𝓝 (1-1)) :=
      (show Continuous (fun t : ℝ => 1-t) by fun_prop).continuousAt
    simpa only [sub_self] using he
  have hmatch₁ : (fun t : ℝ => k₁ (t, 0)) =ᶠ[𝓝 1]
      fun t => Φ (StripCoordinates.center t) := by
    have hsource := hcenter.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₁)
    filter_upwards [hsource, haxis₁.comp_tendsto hrev] with t hs he
    change c₁.map (1-t, 0) = Φ (StripCoordinates.center t)
    change c₁.map (1-t, 0) = α (1-(1-t)) at he
    have he' : 1-(1-t) = t := by ring
    rw [he', ← hzero t hs] at he
    exact he
  obtain ⟨r, hr, V, hV, hrectV, k, hk, hinjk, hmap, _, hik, hcS, hkc, hkk₀, hkk₁, hnormalK⟩ :=
    exists_native_clean_strip_matching_germs Φ hline hclean c₀.smooth hk₁
      c₀.open_domain hU₁ c₀.contains_zero h1U₁ hmatch₀ hmatch₁ hn₀ hn₁' hdim
  have hkc' : ∀ t ∈ Icc (0 : ℝ) 1, k (t, 0) = α t :=
    fun t ht => (hkc t).trans (hzero t (hline ht))
  have hKV : Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ V := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact hrectV ⟨ht, ⟨neg_nonpos.mpr hr.le, hr.le⟩⟩
  have havoidk : ∀ t ∈ Ioo (0 : ℝ) 1, k (t, 0) ∉ T := by
    intro t ht
    rw [hkc' t ⟨ht.1.le, ht.2.le⟩]
    exact havoid t ht
  have hcontact₀ : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), k p ∈ T ↔ p.1 = 0 := by
    filter_upwards [hkk₀, c₀.open_domain.mem_nhds c₀.contains_zero] with p he hp
    rw [he]
    exact (c₀.sheets p hp).2
  have hcontact₁ : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), k p ∈ T ↔ p.1 = 1 := by
    filter_upwards [hkk₁, hU₁.mem_nhds h1U₁] with p he hp
    have h : k p ∈ T ↔ 1-p.1 = 0 := by
      rw [he]
      exact (c₁.sheets (StripCoordinates.reverse p) hp).2
    rw [sub_eq_zero] at h
    exact h.trans eq_comm
  obtain ⟨ε, hε, W, hW, hrectW, hWV, hcT⟩ :=
    exists_strip_neighborhood_with_exact_endpoint_contacts hk hV hKV hT
      havoidk hcontact₀ hcontact₁
  have hemb : IsClosedEmbedding (fun p : Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε => k p) := by
    let R := Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε
    let : CompactSpace R := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
    apply (continuousOn_iff_continuous_domRestrict.mp
      (hk.continuousOn.mono (hrectW.trans hWV))).isClosedEmbedding
    intro p q he
    exact Subtype.ext (hinjk (hWV (hrectW p.property)) (hWV (hrectW q.property)) he)
  let strip : CleanStripPatch (E := E) S T α c₀.map c₁.map := {
    width := ε, width_pos := hε, domain := W, open_domain := hW, contains_strip := hrectW,
    map := k, smooth := hk.mono hWV, injective := hinjk.mono hWV, closed_embedding := hemb,
    derivative_injective := fun p hp => hik p (hWV hp),
    first_sheet := fun p hp => hcS p (hWV hp), second_sheet := hcT,
    center := hkc', left_germ := hkk₀, right_germ := hkk₁ }
  let data : StripNormalData A B (E := E) S k := {
    chart := Φ
    line := hline
    sheet := hclean
    center := hkc
    normal_nonzero := hnormalK }
  exact ⟨strip, ⟨data⟩, fun _ hp => hmap (hWV hp)⟩

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
