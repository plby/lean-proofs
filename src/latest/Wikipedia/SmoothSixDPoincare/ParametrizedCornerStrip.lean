import Wikipedia.SmoothSixDPoincare.EmbeddedArcAmbientChart
import Wikipedia.SmoothSixDPoincare.CornerNormalDerivative
import Wikipedia.SmoothSixDPoincare.NativeStripGerms
import Wikipedia.SmoothSixDPoincare.StripReflection
import Wikipedia.SmoothSixDPoincare.StripEndpointObstacle
import Wikipedia.SmoothSixDPoincare.StripNormalData

/-!
# Shared clean strips with actual parametrized corner germs

The center arc is already constructed. Its corner axes need only agree
with that arc as full germs. The opposite axes use any genuine native sheet
parametrizations. Native transversality then supplies their nonzero normal
derivatives, and the actual clean strip retains both whole corner maps.
-/

noncomputable section

open Set Function Filter Module Metric Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z Z₀ Z₁ N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup Z₀] [NormedSpace ℝ Z₀]
  [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace Z P]
  [T2Space N] [CompactSpace N] [CompactSpace P]

/-- Construct the two-sheet-clean strip, retaining the actual arc and both corner germs. -/
theorem exists_strip_along_arc_matching_parametrized_corners
    {F : N → M} {G : P → M} {f : ℝ → N}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hiF : ∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f) (hinjf : InjOn f (Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t))
    (c₀ : PartialDiffeomorph 𝓘(ℝ, Z₀) 𝓘(ℝ, Z) Z₀ P ∞)
    (c₁ : PartialDiffeomorph 𝓘(ℝ, Z₁) 𝓘(ℝ, Z) Z₁ P ∞)
    (hc₀ : (0 : Z₀) ∈ c₀.source) (hc₁ : (0 : Z₁) ∈ c₁.source)
    (hcross₀ : G (c₀ 0) = F (f 0)) (hcross₁ : G (c₁ 0) = F (f 1))
    (ht₀ : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c₀ 0))))
    (ht₁ : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c₁ 0))))
    (n : ℕ) (hsheet : 1 + n = finrank ℝ D)
    (hcodim : finrank ℝ D + finrank ℝ Z = finrank ℝ E) (hdimZ : 2 ≤ finrank ℝ Z)
    {v₀ : Z₀} {v₁ : Z₁} (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, F (f t) ∉ range G)
    {k₀ k₁ : (ℝ × ℝ) → M} {U₀ U₁ : Set (ℝ × ℝ)}
    (hk₀ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₀ U₀)
    (hk₁ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0U₀ : (0 : ℝ × ℝ) ∈ U₀) (h0U₁ : (0 : ℝ × ℝ) ∈ U₁)
    (hl₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] (F ∘ f))
    (hl₁ : (fun t : ℝ => k₁ (t, 0)) =ᶠ[𝓝 0] fun t => F (f (1 - t)))
    (hr₀ : ∀ s, (0, s) ∈ U₀ → k₀ (0, s) = G (c₀ (s • v₀)))
    (hr₁ : ∀ s, (0, s) ∈ U₁ → k₁ (0, s) = G (c₁ (s • v₁)))
    (hcG₀ : ∀ p ∈ U₀, k₀ p ∈ range G ↔ p.1 = 0)
    (hcG₁ : ∀ p ∈ U₁, k₁ p ∈ range G ↔ p.1 = 0)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo (F ∘ f) (Icc (0 : ℝ) 1) O) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ W : Set (ℝ × ℝ), IsOpen W ∧
      Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε ⊆ W ∧ ∃ k : (ℝ × ℝ) → M,
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧ InjOn k W ∧ MapsTo k W O ∧
        IsClosedEmbedding (fun p : Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε => k p) ∧
        (∀ p ∈ W, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
        (∀ p ∈ W, k p ∈ range F ↔ p.2 = 0) ∧
        (∀ p ∈ W, k p ∈ range G ↔ p.1 = 0 ∨ p.1 = 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, k (t, 0) = F (f t)) ∧
        (k =ᶠ[𝓝 (0, 0)] k₀) ∧ (k =ᶠ[𝓝 (1, 0)] k₁ ∘ StripCoordinates.reverse) ∧
        Nonempty (StripNormalData (EuclideanSpace ℝ (Fin n))
          (EuclideanSpace ℝ (Fin (finrank ℝ Z))) (E := E) (range F) k) := by
  obtain ⟨Φ, hline, htarget, hzero, hclean⟩ :=
    exists_clean_ambient_chart_along_embedded_arc hF hembF hiF hf hinjf hif
      n (finrank ℝ Z) hsheet hcodim hO hfO
  have hline₀ := hline (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have hline₁ := hline (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have hx₀ : F (f 0) ∈ Φ.target := by
    have h := Φ.map_source' hline₀
    rwa [hzero 0 hline₀] at h
  have hx₁ : F (f 1) ∈ Φ.target := by
    have h := Φ.map_source' hline₁
    rwa [hzero 1 hline₁] at h
  have hdim : finrank ℝ Z = finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ Z))) :=
    finrank_euclideanSpace_fin.symm
  have hn₀ := (TransverseCoordinates.corner_normalDerivative_ne_zero Φ hF hG hclean
    c₀ hc₀ hx₀ hcross₀ ht₀ hdim hk₀ hU₀ h0U₀ hv₀ hr₀).1
  have hn₁ := (TransverseCoordinates.corner_normalDerivative_ne_zero Φ hF hG hclean
    c₁ hc₁ hx₁ hcross₁ ht₁ hdim hk₁ hU₁ h0U₁ hv₁ hr₁).1
  let k₁' := k₁ ∘ StripCoordinates.reverse
  let U₁' := StripCoordinates.reverse ⁻¹' U₁
  have hU₁' : IsOpen U₁' := hU₁.preimage StripCoordinates.contDiff_reverse.continuous
  have h1U₁' : (1, 0) ∈ U₁' := by
    change StripCoordinates.reverse (1, 0) ∈ U₁
    rw [StripCoordinates.reverse_one_zero]
    exact h0U₁
  have hk₁' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁' U₁' :=
    hk₁.comp StripCoordinates.contDiff_reverse.contMDiff.contMDiffOn (fun _ hp => hp)
  have hk₁zero : k₁ (0, 0) = F (f 1) := by
    simpa only [sub_zero] using hl₁.eq_of_nhds
  have hk₁Phi : k₁ (0, 0) ∈ Φ.target := hk₁zero.symm ▸ hx₁
  have hnormal := (TransverseCoordinates.contMDiffOn_normalCoordinate Φ).contMDiffAt
    (Φ.open_target.mem_nhds hk₁Phi)
  have hH₁ : DifferentiableAt ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁) (0, 0) :=
    (hnormal.comp (0, 0) (hk₁.contMDiffAt (hU₁.mem_nhds h0U₁))).contDiffAt.differentiableAt
      (by simp)
  have hn₁' : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁') (1, 0) (0, 1) ≠ 0 := by
    change fderiv ℝ ((TransverseCoordinates.normalCoordinate Φ ∘ k₁) ∘
      StripCoordinates.reverse) (1, 0) (0, 1) ≠ 0
    rw [StripCoordinates.vertical_derivative_reverse hH₁]
    exact hn₁
  have hcenter : Continuous (StripCoordinates.center : ℝ →
      StripCoordinates.Space (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin (finrank ℝ Z)))) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hmatch₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] fun t => Φ (StripCoordinates.center t) := by
    have hsource := hcenter.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₀)
    filter_upwards [hsource, hl₀] with t hs heq
    exact heq.trans (hzero t hs).symm
  have hrev : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
      (show Continuous (fun t : ℝ => 1 - t) by fun_prop).continuousAt
    simpa only [sub_self] using he
  have hmatch₁ : (fun t : ℝ => k₁' (t, 0)) =ᶠ[𝓝 1] fun t => Φ (StripCoordinates.center t) := by
    have hsource := hcenter.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₁)
    have hleft := hl₁.comp_tendsto hrev
    filter_upwards [hsource, hleft] with t hs heq
    change k₁ (1 - t, 0) = Φ (StripCoordinates.center t)
    change k₁ (1 - t, 0) = F (f (1 - (1 - t))) at heq
    rw [heq, hzero t hs]
    congr 2
    ring
  obtain ⟨a, ha, V, hV, hrectV, k, hk, hinjk, hmap, _, hik, hcF, hkc, hkk₀, hkk₁,
      hnormal⟩ :=
    exists_native_clean_strip_matching_germs Φ hline hclean hk₀ hk₁'
      hU₀ hU₁' h0U₀ h1U₁' hmatch₀ hmatch₁ hn₀ hn₁'
      (by simpa only [finrank_euclideanSpace_fin] using hdimZ)
  have hkc' : ∀ t ∈ Icc (0 : ℝ) 1, k (t, 0) = F (f t) := by
    intro t ht
    exact (hkc t).trans (hzero t (hline ht))
  have hKV : Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ V := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact hrectV ⟨ht, ⟨neg_nonpos.mpr ha.le, ha.le⟩⟩
  have havoidk : ∀ t ∈ Ioo (0 : ℝ) 1, k (t, 0) ∉ range G := by
    intro t ht
    rw [hkc' t ⟨ht.1.le, ht.2.le⟩]
    exact havoid t ht
  have hcontact₀ : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), k p ∈ range G ↔ p.1 = 0 := by
    filter_upwards [hkk₀, hU₀.mem_nhds h0U₀] with p heq hp
    rw [heq]
    exact hcG₀ p hp
  have hcontact₁ : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), k p ∈ range G ↔ p.1 = 1 := by
    filter_upwards [hkk₁, hU₁'.mem_nhds h1U₁'] with p heq hp
    have h : k p ∈ range G ↔ (StripCoordinates.reverse p).1 = 0 := by
      rw [heq]
      exact hcG₁ (StripCoordinates.reverse p) hp
    change (k p ∈ range G ↔ 1 - p.1 = 0) at h
    rw [sub_eq_zero] at h
    exact h.trans eq_comm
  obtain ⟨ε, hε, W, hW, hrectW, hWV, hcG⟩ :=
    exists_strip_neighborhood_with_exact_endpoint_contacts hk hV hKV
      (isCompact_range hG.continuous).isClosed havoidk hcontact₀ hcontact₁
  have hemb : IsClosedEmbedding (fun p : Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε => k p) := by
    let R := Icc (0 : ℝ) 1 ×ˢ Icc (-ε) ε
    let : CompactSpace R := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
    apply (continuousOn_iff_continuous_domRestrict.mp
      (hk.continuousOn.mono (hrectW.trans hWV))).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjk (hWV (hrectW p.property)) (hWV (hrectW q.property)) hpq)
  exact ⟨ε, hε, W, hW, hrectW, k, hk.mono hWV, hinjk.mono hWV,
    fun _ hp => htarget (hmap (hWV hp)), hemb, fun p hp => hik p (hWV hp),
    fun p hp => hcF p (hWV hp), hcG, hkc', hkk₀, hkk₁,
    ⟨{ chart := Φ
       line := hline
       sheet := hclean
       center := hkc
       normal_nonzero := hnormal }⟩⟩


end Wikipedia.SmoothSixDPoincare
