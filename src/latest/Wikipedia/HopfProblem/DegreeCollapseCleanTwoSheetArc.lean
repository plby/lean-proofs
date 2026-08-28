import Wikipedia.HopfProblem.DegreeCollapseChartAxisCurve

/-!
# A clean arc between two original two-dimensional sheets in dimension five

Construct both endpoint charts from the embedded immersive sheets. The
longitudinal axis is normal to each sheet, with complementary transverse
factors at the two ends. Relative general position constructs an embedded
arc retaining both axis germs and meeting each full sheet only at its own
endpoint. Neither the charts nor the clean arc are supplied as input.
-/

noncomputable section

open Set Function Filter Metric ContinuousMap Topology
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "W₅" => ℝ × (D₂ × D₂)

variable {E M X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [TopologicalSpace X] [ChartedSpace D₂ X] [IsManifold (𝓡 2) ∞ X]
  [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Y] [ChartedSpace D₂ Y] [IsManifold (𝓡 2) ∞ Y]
  [CompactSpace Y] [SecondCountableTopology Y]

theorem exists_clean_two_sheet_arc {f : X → M} {g : Y → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : IsEmbedding f) (hge : IsEmbedding g)
    (hfi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hx : f x ∉ range g) (hy : g y ∉ range f) (γ : Path (f x) (g y)) :
    ∃ Φ Ψ : PartialDiffeomorph 𝓘(ℝ, W₅) 𝓘(ℝ, E) W₅ M ∞,
      (0 : W₅) ∈ Φ.source ∧ ((1 : ℝ), (0 : D₂ × D₂)) ∈ Ψ.source ∧
      Φ 0 = f x ∧ Ψ (1, 0) = g y ∧
      Φ.target ⊆ (range g)ᶜ ∧ Ψ.target ⊆ (range f)ᶜ ∧
      (∀ z ∈ Φ.source, Φ z ∈ range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
      (∀ z ∈ Ψ.source, Ψ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
      ∃ a : C(ℝ, M), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a ∧
        (a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ (t, 0)) ∧
        (a =ᶠ[𝓝 (1 : ℝ)] fun t => Ψ (t, 0)) ∧
        IsClosedEmbedding (fun t : unitInterval => a t) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, a t ∈ range f ↔ t = 0) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, a t ∈ range g ↔ t = 1) := by
  have hclosedf : IsClosed (range f) := (isCompact_range hf.continuous).isClosed
  have hclosedg : IsClosed (range g) := (isCompact_range hg.continuous).isClosed
  have hcodim : Module.finrank ℝ D₂ + (1 + 2) = Module.finrank ℝ E := by
    rw [finrank_euclideanSpace_fin, hdim]
  obtain ⟨Φ, hΦ0, hΦx, hΦavoid, hΦrec⟩ :=
    exists_clean_sheet_axis_chart hf hfe hfi 2 hcodim x hclosedg.isOpen_compl hx
  obtain ⟨Q, hQ0, hQy, hQavoid, hQrec⟩ :=
    exists_clean_sheet_axis_chart hg hge hgi 2 hcodim y hclosedf.isOpen_compl hy
  let T := terminalSheetCoordinates (D := D₂)
  let Ψ := T.toPartialDiffeomorph.trans Q
  have hT1 : T ((1 : ℝ), (0 : D₂ × D₂)) = 0 := by
    change ((1 : ℝ) - 1, ((0 : D₂), (0 : D₂))) = 0
    rw [sub_self]
    rfl
  have hΨ1 : ((1 : ℝ), (0 : D₂ × D₂)) ∈ Ψ.source := by
    refine ⟨mem_univ _, ?_⟩
    change T (1, 0) ∈ Q.source
    rw [hT1]
    exact hQ0
  have hΨy : Ψ (1, 0) = g y := by
    change Q (T (1, 0)) = g y
    rw [hT1]
    exact hQy
  have hΨavoid : Ψ.target ⊆ (range f)ᶜ := fun z hz => hQavoid hz.1
  have hΨrec : ∀ z ∈ Ψ.source, Ψ z ∈ range g ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    intro z hz
    change Q (T z) ∈ range g ↔ _
    rw [hQrec (T z) hz.2]
    change z.1 - 1 = 0 ∧ z.2.1 = 0 ↔ _
    rw [sub_eq_zero]
  let o : C(X ⊕ Y, M) := ⟨Sum.elim f g, hf.continuous.sumElim hg.continuous⟩
  have ho : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ o := hf.sumElim hg
  have horange : range o = range f ∪ range g := by
    ext z
    constructor
    · rintro ⟨a | b, he⟩
      · exact Or.inl ⟨a, he⟩
      · exact Or.inr ⟨b, he⟩
    · rintro (⟨a, he⟩ | ⟨b, he⟩)
      · exact ⟨Sum.inl a, he⟩
      · exact ⟨Sum.inr b, he⟩
  have hoclosed : IsClosed (range o) := by rw [horange]; exact hclosedf.union hclosedg
  obtain ⟨U, hU, h0U, hUΦ, ha, hia⟩ := chart_axis_curve_properties Φ 0 hΦ0
  obtain ⟨W, hW, h1W, hWΨ, hb, hib⟩ := chart_axis_curve_properties Ψ 1 hΨ1
  have hclean0 : ∀ᶠ t in 𝓝 (0 : ℝ), Φ (t, (0 : D₂ × D₂)) ∈ range o → t = 0 := by
    filter_upwards [hU.mem_nhds h0U] with t ht
    rw [horange]
    rintro (h | h)
    · exact ((hΦrec (t, 0) (hUΦ t ht)).mp h).1
    · exact (hΦavoid (Φ.map_source' (hUΦ t ht)) h).elim
  have hclean1 : ∀ᶠ t in 𝓝 (1 : ℝ), Ψ (t, (0 : D₂ × D₂)) ∈ range o → t = 1 := by
    filter_upwards [hW.mem_nhds h1W] with t ht
    rw [horange]
    rintro (h | h)
    · exact (hΨavoid (Ψ.map_source' (hWΨ t ht)) h).elim
    · exact ((hΨrec (t, 0) (hWΨ t ht)).mp h).1
  have hxy : f x ≠ g y := fun h => hx ⟨y, h.symm⟩
  have hends : Φ (0, 0) ≠ Ψ (1, 0) := by
    change Φ 0 ≠ Ψ (1, 0)
    rw [hΦx, hΨy]
    exact hxy
  obtain ⟨a, ha', hleft, hright, hemb, hi, havoid⟩ :=
    exists_clean_arc_with_local_endpoint_germs ha hb hU hW h0U h1W hia hib
      (γ.cast hΦx hΨy) hends (by omega) o ho hoclosed
      (by rw [finrank_euclideanSpace_fin, hdim]; norm_num) hclean0 hclean1
  have ha0 : a 0 = f x := hleft.eq_of_nhds.trans hΦx
  have ha1 : a 1 = g y := hright.eq_of_nhds.trans hΨy
  refine ⟨Φ, Ψ, hΦ0, hΨ1, hΦx, hΨy, hΦavoid, hΨavoid, hΦrec, hΨrec,
    a, ha', hleft, hright, hemb, hi, ?_, ?_⟩
  · intro t ht
    constructor
    · intro h
      by_contra ht0
      have ht1 : t ≠ 1 := by intro he; subst t; rw [ha1] at h; exact hy h
      exact havoid t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
        (horange.symm ▸ Or.inl h)
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
        (horange.symm ▸ Or.inr h)
    · intro he
      subst t
      rw [ha1]
      exact mem_range_self y

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
