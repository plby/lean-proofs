import Wikipedia.SmoothSixDPoincare.CompactEmbeddedAvoidance
import Wikipedia.SmoothSixDPoincare.RelativeCurveHomotopy

/-!
# A second obstacle can be avoided without losing the first clean arc

Only a compact middle interval is moved. Its image stays in the complement
of the first closed obstacle. The whole endpoint germs remain fixed,
and the global no-new-coincidence property preserves the original embedded
arc. The second obstacle can have a different dimension from the first.
-/

noncomputable section

open Set Function Filter Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

variable {G V H H' N Y : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ G H} {I : ModelWithCorners ℝ V H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I ∞ Y]
  [SecondCountableTopology Y]

theorem exists_arc_avoiding_second_obstacle_controlled (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hemb : IsClosedEmbedding (fun t : unitInterval => f t))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    {S : Set N} (hS : IsClosed S) (hfirst : ∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ S)
    (o : C(Y, N)) (ho : ContMDiff I J ∞ o) (hclosed : IsClosed (range o))
    (hdim : 3 ≤ Module.finrank ℝ G) (hobdim : 1 + Module.finrank ℝ V < Module.finrank ℝ G)
    (hclean0 : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ range o → t = 0)
    (hclean1 : ∀ᶠ t in 𝓝 (1 : ℝ), f t ∈ range o → t = 1) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
      (g =ᶠ[𝓝 (0 : ℝ)] f) ∧ (g =ᶠ[𝓝 (1 : ℝ)] f) ∧
      IsClosedEmbedding (fun t : unitInterval => g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J g t)) ∧
      f.HomotopicRel g {0, 1} ∧
      (∃ C : Set ℝ, IsClosed C ∧ C ∈ 𝓝 (0 : ℝ) ∧ C ∈ 𝓝 (1 : ℝ) ∧
        HomotopicRelWithin f g C (Ioo (0 : ℝ) 1) Sᶜ) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, g t ∉ S ∧ g t ∉ range o := by
  obtain ⟨r, hr, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hclean0
  obtain ⟨s, hs, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hclean1
  let δ : ℝ := min (min r s) (1 / 4)
  have hδ : 0 < δ := lt_min (lt_min hr hs) (by norm_num)
  have hδr : δ ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hδs : δ ≤ s := (min_le_left _ _).trans (min_le_right _ _)
  have hleft (t : ℝ) (ht : 0 < t ∧ t ≤ δ) : f t ∉ range o := by
    intro hto
    have htball : t ∈ closedBall (0 : ℝ) r := by
      rw [mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos ht.1]
      exact ht.2.trans hδr
    exact ht.1.ne' (hball0 htball hto)
  have hright (t : ℝ) (ht : 1 - δ ≤ t ∧ t < 1) : f t ∉ range o := by
    intro hto
    have htball : t ∈ closedBall (1 : ℝ) s := by
      rw [mem_closedBall, Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2)]
      linarith
    exact ht.2.ne (hball1 htball hto)
  let K : Set ℝ := Icc δ (1 - δ)
  let C : Set ℝ := (Ioo δ (1 - δ))ᶜ
  have hKunit : K ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨hδ.le.trans ht.1, ht.2.trans (by linarith)⟩
  have hKopen : K ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    exact ⟨hδ.trans_le ht.1, ht.2.trans_lt (by linarith)⟩
  have hfixed : ∀ t ∈ K ∩ C, f t ∉ o '' univ := by
    intro t ht
    have hends : t = δ ∨ t = 1 - δ := by
      by_cases h : t = δ
      · exact Or.inl h
      · right
        have hlo : δ < t := lt_of_le_of_ne ht.1.1 (Ne.symm h)
        have hn : ¬ t < 1 - δ := fun hu => ht.2 ⟨hlo, hu⟩
        exact le_antisymm ht.1.2 (not_lt.mp hn)
    rw [image_univ]
    rcases hends with rfl | rfl
    · exact hleft δ ⟨hδ, le_rfl⟩
    · exact hright (1 - δ) ⟨le_rfl, by linarith⟩
  have hinj : InjOn f K := by
    intro t ht u hu htu
    exact congrArg Subtype.val
      (hemb.injective (a₁ := ⟨t, hKunit ht⟩) (a₂ := ⟨u, hKunit hu⟩) htu)
  obtain ⟨g, hg, hcontrolled, _, hgi, hnoNew, hmaps, havoid⟩ :=
    exists_embedded_avoidance_on_compact_of_isClosed_image_controlled f o univ hf ho
      (by simpa only [image_univ] using hclosed)
      (by simpa only [Module.finrank_self] using (show 2 < Module.finrank ℝ G by omega))
      (by simpa only [Module.finrank_self] using hobdim)
      (isCompact_Icc (a := δ) (b := 1 - δ)) (isCompact_Icc (a := δ) (b := 1 - δ))
      isOpen_Ioo.isClosed_compl hinj (fun t ht => hi t (hKunit ht)) hfixed
      hS.isOpen_compl (fun t ht => hfirst t (hKopen ht))
  have hrel := hcontrolled.homotopicRel
  have hfg (t : ℝ) (ht : t ∉ K) : g =ᶠ[𝓝 t] f := by
    have hCt : C ∈ 𝓝 t := mem_of_superset (isClosed_Icc.isOpen_compl.mem_nhds ht)
      (compl_subset_compl.mpr Ioo_subset_Icc_self)
    filter_upwards [hCt] with u hu
    exact (hrel.fst_eq_snd hu).symm
  have h0K : (0 : ℝ) ∉ K := fun ht => (not_le_of_gt hδ) ht.1
  have h1K : (1 : ℝ) ∉ K := by intro ht; have h := ht.2; linarith
  have h0C : C ∈ 𝓝 (0 : ℝ) :=
    mem_of_superset (isClosed_Icc.isOpen_compl.mem_nhds h0K)
      (compl_subset_compl.mpr Ioo_subset_Icc_self)
  have h1C : C ∈ 𝓝 (1 : ℝ) :=
    mem_of_superset (isClosed_Icc.isOpen_compl.mem_nhds h1K)
      (compl_subset_compl.mpr Ioo_subset_Icc_self)
  have hfull : HomotopicRelWithin f g C (Ioo (0 : ℝ) 1) Sᶜ := by
    apply hcontrolled.extend_source ?_ hfirst
    intro t _
    by_cases htK : t ∈ K
    · exact Or.inl htK
    · exact Or.inr (fun ht => htK (Ioo_subset_Icc_self ht))
  have hends : ({0, 1} : Set ℝ) ⊆ C := by
    intro t ht
    rcases ht with rfl | ht
    · exact fun h => h0K (Ioo_subset_Icc_self h)
    · have ht1 : t = 1 := ht
      subst t
      exact fun h => h1K (Ioo_subset_Icc_self h)
  refine ⟨g, hg, hfg 0 h0K, hfg 1 h1K, ?_, ?_,
    CurveImmersion.homotopicRel_mono hrel hends,
    ⟨C, isOpen_Ioo.isClosed_compl, h0C, h1C, hfull⟩, ?_⟩
  · apply (g.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro t u htu
    exact hemb.injective (hnoNew t u htu)
  · intro t ht
    by_cases htK : t ∈ K
    · exact hgi t htK
    · rw [(hfg t htK).mfderiv_eq]
      exact hi t ht
  · intro t ht
    constructor
    · by_cases htK : t ∈ K
      · exact hmaps htK
      · exact (hfg t htK).eq_of_nhds ▸ hfirst t ht
    · rw [← image_univ]
      apply havoid t
      by_cases htK : t ∈ K
      · exact Or.inr htK
      · left
        rw [image_univ]
        by_cases htδ : t ≤ δ
        · exact hleft t ⟨ht.1, htδ⟩
        · have htt : 1 - δ < t := by
            apply lt_of_not_ge
            intro hh
            exact htK ⟨(lt_of_not_ge htδ).le, hh⟩
          exact hright t ⟨htt.le, ht.2⟩

/-- The original second-obstacle theorem follows by forgetting the stronger trace control. -/
theorem exists_arc_avoiding_second_obstacle (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hemb : IsClosedEmbedding (fun t : unitInterval => f t))
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    {S : Set N} (hS : IsClosed S) (hfirst : ∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ S)
    (o : C(Y, N)) (ho : ContMDiff I J ∞ o) (hclosed : IsClosed (range o))
    (hdim : 3 ≤ Module.finrank ℝ G) (hobdim : 1 + Module.finrank ℝ V < Module.finrank ℝ G)
    (hclean0 : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ range o → t = 0)
    (hclean1 : ∀ᶠ t in 𝓝 (1 : ℝ), f t ∈ range o → t = 1) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
      (g =ᶠ[𝓝 (0 : ℝ)] f) ∧ (g =ᶠ[𝓝 (1 : ℝ)] f) ∧
      IsClosedEmbedding (fun t : unitInterval => g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J g t)) ∧
      f.HomotopicRel g {0, 1} ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, g t ∉ S ∧ g t ∉ range o := by
  obtain ⟨g, hg, h0, h1, he, hi, hrel, _, havoid⟩ :=
    exists_arc_avoiding_second_obstacle_controlled f hf hemb hi hS hfirst o ho hclosed
      hdim hobdim hclean0 hclean1
  exact ⟨g, hg, h0, h1, he, hi, hrel, havoid⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
