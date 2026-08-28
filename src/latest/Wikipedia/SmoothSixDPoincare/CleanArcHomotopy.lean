import Wikipedia.SmoothSixDPoincare.ArcSecondObstacleAvoidance
import Wikipedia.SmoothSixDPoincare.CurveEndpointNeighborhood
import Wikipedia.SmoothSixDPoincare.RelativeCurveAvoidance

/-!
# Clean arcs retain the original smooth curve's endpoint-relative homotopy class

Construct clean fixed endpoint neighborhoods before embedding and avoiding
the first sheet. A second, possibly differently dimensional sheet can then
be avoided without changing the first avoidance or the based path class.
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
  [CompactSpace Y] [SecondCountableTopology Y]

theorem exists_clean_arc_homotopicRel (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hxy : f 0 ≠ f 1) (hi0 : Injective (mfderiv 𝓘(ℝ, ℝ) J f 0))
    (hi1 : Injective (mfderiv 𝓘(ℝ, ℝ) J f 1))
    (o : C(Y, N)) (ho : ContMDiff I J ∞ o)
    (hdim : 3 ≤ Module.finrank ℝ G) (hobdim : 1 + Module.finrank ℝ V < Module.finrank ℝ G)
    (hclean0 : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ range o → t = 0)
    (hclean1 : ∀ᶠ t in 𝓝 (1 : ℝ), f t ∈ range o → t = 1) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
      (g =ᶠ[𝓝 (0 : ℝ)] f) ∧ (g =ᶠ[𝓝 (1 : ℝ)] f) ∧
      IsClosedEmbedding (fun t : unitInterval => g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J g t)) ∧
      f.HomotopicRel g {0, 1} ∧ ∀ t ∈ Ioo (0 : ℝ) 1, g t ∉ range o := by
  obtain ⟨C₀, hC₀, hBC₀, hinj₀, hd₀, _⟩ :=
    exists_clean_curve_endpoint_neighborhood hf hxy hi0 hi1 (S := ∅) finite_empty
  obtain ⟨r, hr, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hclean0
  obtain ⟨s, hs, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hclean1
  let C : Set ℝ := C₀ ∩ (closedBall 0 r ∪ closedBall 1 s)
  have hC : IsClosed C := hC₀.isClosed.inter (isClosed_closedBall.union isClosed_closedBall)
  have h0C : C ∈ 𝓝 (0 : ℝ) := inter_mem
    (mem_interior_iff_mem_nhds.mp (hBC₀ (by simp)))
    (mem_of_superset (closedBall_mem_nhds 0 hr) subset_union_left)
  have h1C : C ∈ 𝓝 (1 : ℝ) := inter_mem
    (mem_interior_iff_mem_nhds.mp (hBC₀ (by simp)))
    (mem_of_superset (closedBall_mem_nhds 1 hs) subset_union_right)
  have hBC : ({0, 1} : Set ℝ) ⊆ interior C := by
    intro t ht
    rcases ht with rfl | ht
    · exact mem_interior_iff_mem_nhds.mpr h0C
    · have ht1 : t = 1 := ht
      subst t
      exact mem_interior_iff_mem_nhds.mpr h1C
  have hclean : ∀ t ∈ Icc (0 : ℝ) 1 ∩ C,
      t ∉ ({0, 1} : Set ℝ) → f t ∉ range o := by
    intro t ht htn hto
    rcases ht.2.2 with hleft | hright
    · exact htn (Or.inl (hball0 hleft hto))
    · exact htn (Or.inr (hball1 hright hto))
  obtain ⟨g, hg, hrel, hemb, hi, havoid⟩ :=
    exists_relative_curve_avoidance_of_clean_neighborhood f o hf ho hdim hobdim
      isCompact_Icc hC hBC
      (hinj₀.mono (fun _ ht => ht.2.1)) (fun t ht => hd₀ t ht.2.1) hclean
  have hgf (t : ℝ) (ht : C ∈ 𝓝 t) : g =ᶠ[𝓝 t] f := by
    filter_upwards [ht] with u hu
    exact (hrel.fst_eq_snd hu).symm
  refine ⟨g, hg, hgf 0 h0C, hgf 1 h1C, hemb, hi,
    CurveImmersion.homotopicRel_mono hrel (hBC.trans interior_subset), ?_⟩
  intro t ht
  apply havoid t ⟨⟨ht.1.le, ht.2.le⟩, ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  exact ⟨ht.1.ne', ht.2.ne⟩

variable {V₂ H₂ Y₂ : Type*}
  [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [FiniteDimensional ℝ V₂]
  [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ V₂ H₂}
  [TopologicalSpace Y₂] [ChartedSpace H₂ Y₂] [IsManifold I₂ ∞ Y₂]
  [SecondCountableTopology Y₂]

theorem exists_clean_arc_two_images_homotopicRel (f : C(ℝ, N))
    (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f) (hxy : f 0 ≠ f 1)
    (hi0 : Injective (mfderiv 𝓘(ℝ, ℝ) J f 0))
    (hi1 : Injective (mfderiv 𝓘(ℝ, ℝ) J f 1))
    (o₁ : C(Y, N)) (ho₁ : ContMDiff I J ∞ o₁)
    (o₂ : C(Y₂, N)) (ho₂ : ContMDiff I₂ J ∞ o₂) (hc₂ : IsClosed (range o₂))
    (hdim : 3 ≤ Module.finrank ℝ G)
    (hd₁ : 1 + Module.finrank ℝ V < Module.finrank ℝ G)
    (hd₂ : 1 + Module.finrank ℝ V₂ < Module.finrank ℝ G)
    (ha₁ : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ range o₁ → t = 0)
    (hb₁ : ∀ᶠ t in 𝓝 (1 : ℝ), f t ∈ range o₁ → t = 1)
    (ha₂ : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ range o₂ → t = 0)
    (hb₂ : ∀ᶠ t in 𝓝 (1 : ℝ), f t ∈ range o₂ → t = 1) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
      (g =ᶠ[𝓝 (0 : ℝ)] f) ∧ (g =ᶠ[𝓝 (1 : ℝ)] f) ∧
      IsClosedEmbedding (fun t : unitInterval => g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J g t)) ∧
      f.HomotopicRel g {0, 1} ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, g t ∉ range o₁ ∧ g t ∉ range o₂ := by
  obtain ⟨a, ha, haf0, haf1, hae, hai, hfa, havoid⟩ :=
    exists_clean_arc_homotopicRel f hf hxy hi0 hi1 o₁ ho₁ hdim hd₁ ha₁ hb₁
  have hclean0 : ∀ᶠ t in 𝓝 (0 : ℝ), a t ∈ range o₂ → t = 0 := by
    filter_upwards [haf0, ha₂] with t ht hclean
    rw [ht]
    exact hclean
  have hclean1 : ∀ᶠ t in 𝓝 (1 : ℝ), a t ∈ range o₂ → t = 1 := by
    filter_upwards [haf1, hb₂] with t ht hclean
    rw [ht]
    exact hclean
  obtain ⟨g, hg, hga0, hga1, hge, hgi, hag, hgavoid⟩ :=
    exists_arc_avoiding_second_obstacle a ha hae hai
      (isCompact_range o₁.continuous).isClosed havoid o₂ ho₂ hc₂ hdim hd₂ hclean0 hclean1
  exact ⟨g, hg, hga0.trans haf0, hga1.trans haf1, hge, hgi, hfa.trans hag, hgavoid⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
