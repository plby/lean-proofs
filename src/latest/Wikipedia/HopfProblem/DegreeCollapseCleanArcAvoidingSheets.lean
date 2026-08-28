import Wikipedia.HopfProblem.DegreeCollapseCleanSheetPassage

/-!
# A clean connecting arc avoiding all protected sheet images

An additional closed smooth surface image may contain all other handle
spheres. Relative avoidance is applied to its union with the two selected
sheet images. The actual endpoint charts and their full axis germs survive,
and the entire closed connecting arc avoids the protected image.
-/

noncomputable section

open Set Function Filter Metric ContinuousMap Topology
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "W₅" => ℝ × (D₂ × D₂)

variable {E M X Y Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [ChartedSpace D₂ X] [IsManifold (𝓡 2) ∞ X]
  [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [ChartedSpace D₂ Y] [IsManifold (𝓡 2) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]
  [TopologicalSpace Z] [ChartedSpace D₂ Z] [IsManifold (𝓡 2) ∞ Z]
  [SecondCountableTopology Z]

theorem exists_clean_two_sheet_arc_avoiding {f : X → M} {g : Y → M} {b : Z → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : IsEmbedding f) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b) (hbc : IsClosed (range b))
    (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hx : f x ∉ range g) (hy : g y ∉ range f)
    (hbx : f x ∉ range b) (hby : g y ∉ range b) (γ : Path (f x) (g y)) :
    ∃ Φ Ψ : PartialDiffeomorph 𝓘(ℝ, W₅) 𝓘(ℝ, E) W₅ M ∞,
      (0 : W₅) ∈ Φ.source ∧ ((1 : ℝ), (0 : D₂ × D₂)) ∈ Ψ.source ∧
      Φ 0 = f x ∧ Ψ (1, 0) = g y ∧
      (∀ z ∈ Φ.source, Φ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
      (∀ z ∈ Ψ.source, Ψ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
      ∃ a : C(ℝ, M), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a ∧
        (a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ (t, 0)) ∧
        (a =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0)) ∧
        IsClosedEmbedding (fun t : unitInterval => a t) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, a t ∈ range f ↔ t = 0) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, a t ∈ range g ↔ t = 1) ∧
        MapsTo a (Icc (0 : ℝ) 1) (range b)ᶜ := by
  obtain ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦavoid, hΨavoid, hΦrec, hΨrec, -⟩ :=
    exists_clean_two_sheet_arc hf hg hfe hge hfi hgi hdim x y hx hy γ
  let o : C((X ⊕ Y) ⊕ Z, M) :=
    ⟨Sum.elim (Sum.elim f g) b, (hf.continuous.sumElim hg.continuous).sumElim hb.continuous⟩
  have ho : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ o := (hf.sumElim hg).sumElim hb
  have horange : range o = (range f ∪ range g) ∪ range b := by
    ext z
    constructor
    · rintro ⟨(a | c) | d, he⟩
      · exact Or.inl (Or.inl ⟨a, he⟩)
      · exact Or.inl (Or.inr ⟨c, he⟩)
      · exact Or.inr ⟨d, he⟩
    · rintro ((⟨a, he⟩ | ⟨c, he⟩) | ⟨d, he⟩)
      · exact ⟨Sum.inl (Sum.inl a), he⟩
      · exact ⟨Sum.inl (Sum.inr c), he⟩
      · exact ⟨Sum.inr d, he⟩
  have hoclosed : IsClosed (range o) := by
    rw [horange]
    exact ((isCompact_range hf.continuous).isClosed.union
      (isCompact_range hg.continuous).isClosed).union hbc
  obtain ⟨U, hU, h0U, hUΦ, ha, hia⟩ := chart_axis_curve_properties Φ 0 hΦ0
  obtain ⟨V, hV, h1V, hVΨ, hc, hic⟩ := chart_axis_curve_properties Ψ 1 hΨ1
  have hnear0 : ∀ᶠ t in 𝓝 (0 : ℝ), Φ (t, (0 : D₂ × D₂)) ∉ range b :=
    (ha.contMDiffAt (hU.mem_nhds h0U)).continuousAt.eventually
      (hbc.isOpen_compl.mem_nhds (by change Φ 0 ∉ range b; rw [hΦx]; exact hbx))
  have hnear1 : ∀ᶠ t in 𝓝 (1 : ℝ), Ψ (t, (0 : D₂ × D₂)) ∉ range b :=
    (hc.contMDiffAt (hV.mem_nhds h1V)).continuousAt.eventually
      (hbc.isOpen_compl.mem_nhds (by change Ψ (1, 0) ∉ range b; rw [hΨy]; exact hby))
  have hclean0 : ∀ᶠ t in 𝓝 (0 : ℝ), Φ (t, (0 : D₂ × D₂)) ∈ range o → t = 0 := by
    filter_upwards [hU.mem_nhds h0U, hnear0] with t ht hb'
    rw [horange]
    rintro ((h | h) | h)
    · exact ((hΦrec (t, 0) (hUΦ t ht)).mp h).1
    · exact (hΦavoid (Φ.map_source' (hUΦ t ht)) h).elim
    · exact (hb' h).elim
  have hclean1 : ∀ᶠ t in 𝓝 (1 : ℝ), Ψ (t, (0 : D₂ × D₂)) ∈ range o → t = 1 := by
    filter_upwards [hV.mem_nhds h1V, hnear1] with t ht hb'
    rw [horange]
    rintro ((h | h) | h)
    · exact (hΨavoid (Ψ.map_source' (hVΨ t ht)) h).elim
    · exact ((hΨrec (t, 0) (hVΨ t ht)).mp h).1
    · exact (hb' h).elim
  have hends : Φ (0, 0) ≠ Ψ (1, 0) := by
    change Φ 0 ≠ Ψ (1, 0)
    rw [hΦx, hΨy]
    exact fun h => hx ⟨y, h.symm⟩
  obtain ⟨a, ha', hleft, hright, hemb, hi, havoid⟩ :=
    exists_clean_arc_with_local_endpoint_germs ha hc hU hV h0U h1V hia hic
      (γ.cast hΦx hΨy) hends (by omega) o ho hoclosed
      (by rw [finrank_euclideanSpace_fin, hdim]; norm_num) hclean0 hclean1
  have ha0 : a 0 = f x := hleft.eq_of_nhds.trans hΦx
  have ha1 : a 1 = g y := hright.eq_of_nhds.trans hΨy
  refine ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦrec, hΨrec,
    a, ha', hleft, hright, hemb, hi, ?_, ?_, ?_⟩
  · intro t ht
    constructor
    · intro h
      by_contra ht0
      have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at h; exact hy h
      exact havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
        (horange.symm ▸ Or.inl (Or.inl h))
    · intro he
      subst t
      rw [ha0]
      exact mem_range_self x
  · intro t ht
    constructor
    · intro h
      by_contra ht1
      have ht0 : t ≠ 0 := by intro he; subst t; rw [ha0] at h; exact hx h
      exact havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
        (horange.symm ▸ Or.inl (Or.inr h))
    · intro he
      subst t
      rw [ha1]
      exact mem_range_self y
  · intro t ht htb
    have ht0 : t ≠ 0 := by intro he; subst t; rw [ha0] at htb; exact hbx htb
    have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at htb; exact hby htb
    exact havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
      (horange.symm ▸ Or.inr htb)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
