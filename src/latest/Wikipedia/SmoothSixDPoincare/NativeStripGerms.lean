import Wikipedia.SmoothSixDPoincare.LocalStripGerms
import Wikipedia.SmoothSixDPoincare.SheetNormalCoordinates

/-!
# Actual native strips matching both full corner germs

Express the given local corner maps in a genuine clean ambient sheet chart,
construct the clean embedded coordinate strip, and compose back with that
same native chart. The complete two-dimensional corner germs are retained,
not just the center arcs or the transverse first derivatives.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {A B E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]

/-- Construct a clean embedded native strip preserving both complete prescribed corner germs. -/
theorem exists_native_clean_strip_matching_germs
    (Φ : PartialDiffeomorph 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E)
      (StripCoordinates.Space A B) M ∞)
    (hline : MapsTo StripCoordinates.center (Icc (0 : ℝ) 1) Φ.source)
    {S : Set M} (hclean : ∀ q ∈ Φ.source, Φ q ∈ S ↔ q.2 = 0)
    {k₀ k₁ : (ℝ × ℝ) → M} {U₀ U₁ : Set (ℝ × ℝ)}
    (hk₀ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₀ U₀)
    (hk₁ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (h0U₀ : (0, 0) ∈ U₀) (h1U₁ : (1, 0) ∈ U₁)
    (hc₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] fun t => Φ (StripCoordinates.center t))
    (hc₁ : (fun t : ℝ => k₁ (t, 0)) =ᶠ[𝓝 1] fun t => Φ (StripCoordinates.center t))
    (hn₀ : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₀) (0, 0) (0, 1) ≠ 0)
    (hn₁ : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁) (1, 0) (0, 1) ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set (ℝ × ℝ), IsOpen W ∧
      Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε ⊆ W ∧ ∃ k : (ℝ × ℝ) → M,
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧ InjOn k W ∧ MapsTo k W Φ.target ∧
        IsClosedEmbedding (fun p : Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε => k p) ∧
        (∀ p ∈ W, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
        (∀ p ∈ W, k p ∈ S ↔ p.2 = 0) ∧
        (∀ t, k (t, 0) = Φ (StripCoordinates.center t)) ∧
        (k =ᶠ[𝓝 (0, 0)] k₀) ∧ (k =ᶠ[𝓝 (1, 0)] k₁) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k) (t, 0) (0, 1) ≠ 0) := by
  let C₀ := U₀ ∩ k₀ ⁻¹' Φ.target
  let C₁ := U₁ ∩ k₁ ⁻¹' Φ.target
  have hC₀ : IsOpen C₀ := hk₀.continuousOn.isOpen_inter_preimage hU₀ Φ.open_target
  have hC₁ : IsOpen C₁ := hk₁.continuousOn.isOpen_inter_preimage hU₁ Φ.open_target
  have hline₀ : StripCoordinates.center (0 : ℝ) ∈ Φ.source := hline (by simp)
  have hline₁ : StripCoordinates.center (1 : ℝ) ∈ Φ.source := hline (by simp)
  have h0C₀ : (0, 0) ∈ C₀ := by
    refine ⟨h0U₀, ?_⟩
    change k₀ (0, 0) ∈ Φ.target
    rw [hc₀.eq_of_nhds]
    exact Φ.map_source' hline₀
  have h1C₁ : (1, 0) ∈ C₁ := by
    refine ⟨h1U₁, ?_⟩
    change k₁ (1, 0) ∈ Φ.target
    rw [hc₁.eq_of_nhds]
    exact Φ.map_source' hline₁
  let G₀ : (ℝ × ℝ) → StripCoordinates.Space A B := Φ.invFun ∘ k₀
  let G₁ : (ℝ × ℝ) → StripCoordinates.Space A B := Φ.invFun ∘ k₁
  have hG₀ : ContDiffOn ℝ ∞ G₀ C₀ :=
    (Φ.contMDiffOn_invFun.comp (hk₀.mono inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  have hG₁ : ContDiffOn ℝ ∞ G₁ C₁ :=
    (Φ.contMDiffOn_invFun.comp (hk₁.mono inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  have hc : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hcG₀ : (fun t : ℝ => G₀ (t, 0)) =ᶠ[𝓝 0] StripCoordinates.center := by
    have hsource := hc.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₀)
    filter_upwards [hc₀, hsource] with t hkt ht
    change Φ.invFun (k₀ (t, 0)) = StripCoordinates.center t
    rw [hkt]
    exact Φ.left_inv' ht
  have hcG₁ : (fun t : ℝ => G₁ (t, 0)) =ᶠ[𝓝 1] StripCoordinates.center := by
    have hsource := hc.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₁)
    filter_upwards [hc₁, hsource] with t hkt ht
    change Φ.invFun (k₁ (t, 0)) = StripCoordinates.center t
    rw [hkt]
    exact Φ.left_inv' ht
  obtain ⟨F, hF, hFc, hFG₀, hFG₁, ε, hε, W, hW, hrect, hinjF, hsource, hiF, hcleanF,
      _, hnormalF⟩ :=
    StripCoordinates.exists_clean_strip_matching_local_germs hG₀ hG₁ hC₀ hC₁ h0C₀ h1C₁
      hcG₀ hcG₁ hn₀ hn₁ hdim Φ.open_source hline
  let k := Φ ∘ F
  have hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W :=
    Φ.contMDiffOn_toFun.comp hF.contMDiff.contMDiffOn hsource
  have hinjk : InjOn k W := by
    intro p hp q hq heq
    exact hinjF hp hq (Φ.toPartialEquiv.injOn (hsource hp) (hsource hq) heq)
  have hemb : IsClosedEmbedding (fun p : Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε => k p) := by
    let R := Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε
    let : CompactSpace R := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
    apply (continuousOn_iff_continuous_domRestrict.mp
      (hk.continuousOn.mono hrect)).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjk (hrect p.property) (hrect q.property) hpq)
  refine ⟨ε, hε, W, hW, hrect, k, hk, hinjk, fun _ hp => Φ.map_source' (hsource hp),
    hemb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hiFM : Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, StripCoordinates.Space A B) F p) := by
      rw [mfderiv_eq_fderiv]
      exact hiF p hp
    change Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Φ ∘ F) p)
    rw [mfderiv_comp p (Φ.mdifferentiableAt (by simp) (hsource hp))
      (hF.contMDiff.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv Φ (hsource hp)).1.comp hiFM
  · intro p hp
    exact (hclean (F p) (hsource hp)).trans (hcleanF p hp)
  · intro t
    exact congrArg Φ (hFc t)
  · filter_upwards [hFG₀, hC₀.mem_nhds h0C₀] with p hFp hp
    change Φ (F p) = k₀ p
    rw [hFp]
    exact Φ.right_inv' hp.2
  · filter_upwards [hFG₁, hC₁.mem_nhds h1C₁] with p hFp hp
    change Φ (F p) = k₁ p
    rw [hFp]
    exact Φ.right_inv' hp.2
  · intro t ht
    have hp : (t, (0 : ℝ)) ∈ W := hrect ⟨ht, ⟨neg_nonpos.mpr hε.le, hε.le⟩⟩
    have heq : (TransverseCoordinates.normalCoordinate Φ ∘ k) =ᶠ[𝓝 (t, 0)]
        (fun p => (F p).2) := by
      filter_upwards [hW.mem_nhds hp] with p hpW
      change (Φ.invFun (Φ (F p))).2 = (F p).2
      rw [Φ.left_inv' (hsource hpW)]
    rw [heq.fderiv_eq]
    exact hnormalF t

end Wikipedia.SmoothSixDPoincare
