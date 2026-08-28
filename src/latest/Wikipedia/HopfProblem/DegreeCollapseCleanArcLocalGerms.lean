import Wikipedia.HopfProblem.DegreeCollapseClosedSubsetDiskAlignment
import Wikipedia.SmoothSixDPoincare.LocalCurveEndpointGerms
import Wikipedia.SmoothSixDPoincare.CleanNeighborhoodAvoidance

/-!
# An embedded connecting arc with clean prescribed endpoint germs

The entire original smooth obstacle is avoided in the open arc. Both
locally defined endpoint curves are retained as full germs, even when their
endpoint values lie on the obstacle. The closed fixed neighborhoods are
constructed from their local isolated-contact properties.
-/

noncomputable section

open Set Function Filter Metric ContinuousMap Topology
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {G V H H' N Y : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ G H} {I : ModelWithCorners ℝ V H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I ∞ Y] [SecondCountableTopology Y]

theorem exists_clean_arc_with_local_endpoint_germs {a b : ℝ → N} {U W : Set ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b W)
    (hU : IsOpen U) (hW : IsOpen W) (h0U : (0 : ℝ) ∈ U) (h1W : (1 : ℝ) ∈ W)
    (hia : Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Injective (mfderiv 𝓘(ℝ, ℝ) J b 1))
    (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1) (hdim : 3 ≤ Module.finrank ℝ G)
    (o : C(Y, N)) (ho : ContMDiff I J ∞ o) (hclosed : IsClosed (range o))
    (hobdim : 1 + Module.finrank ℝ V < Module.finrank ℝ G)
    (hclean0 : ∀ᶠ t in 𝓝 (0 : ℝ), a t ∈ range o → t = 0)
    (hclean1 : ∀ᶠ t in 𝓝 (1 : ℝ), b t ∈ range o → t = 1) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
      (f =ᶠ[𝓝 (0 : ℝ)] a) ∧ (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
      IsClosedEmbedding (fun t : unitInterval => f t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
      ∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ range o := by
  obtain ⟨f, hf, hfa, hfb, hemb, hfd, -⟩ :=
    exists_embedded_arc_with_local_endpoint_germs ha hb hU hW h0U h1W hia hib γ hxy hdim
      (S := ∅) finite_empty
  have hnear0 : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ range o → t = 0 := by
    filter_upwards [hfa, hclean0] with t he hc
    rw [he]
    exact hc
  have hnear1 : ∀ᶠ t in 𝓝 (1 : ℝ), f t ∈ range o → t = 1 := by
    filter_upwards [hfb, hclean1] with t he hc
    rw [he]
    exact hc
  obtain ⟨r, hr, hball0⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear0
  obtain ⟨s, hs, hball1⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear1
  let C : Set ℝ := closedBall 0 r ∪ closedBall 1 s
  have h0C : C ∈ 𝓝 (0 : ℝ) := mem_of_superset (ball_mem_nhds 0 hr)
    (fun _ ht => Or.inl (ball_subset_closedBall ht))
  have h1C : C ∈ 𝓝 (1 : ℝ) := mem_of_superset (ball_mem_nhds 1 hs)
    (fun _ ht => Or.inr (ball_subset_closedBall ht))
  have hBC : ({0, 1} : Set ℝ) ⊆ interior C := by
    intro t ht
    rcases ht with rfl | ht
    · exact mem_interior_iff_mem_nhds.mpr h0C
    · have ht1 : t = 1 := ht
      subst t
      exact mem_interior_iff_mem_nhds.mpr h1C
  have hclean : ∀ t ∈ Icc (0 : ℝ) 1 ∩ C, t ∉ ({0, 1} : Set ℝ) → f t ∉ range o := by
    intro t ht htB hto
    rcases ht.2 with ht0 | ht1
    · exact htB (Or.inl (hball0 ht0 hto))
    · exact htB (Or.inr (hball1 ht1 hto))
  have hfi : InjOn f (Icc (0 : ℝ) 1) := by
    intro x hx y hy he
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) he)
  have hself : 2 * Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Module.finrank_self]
    omega
  have hobs : Module.finrank ℝ ℝ + Module.finrank ℝ V < Module.finrank ℝ G := by
    simpa only [Module.finrank_self] using hobdim
  obtain ⟨g, hg, hrel, hge, hgd, havoid⟩ :=
    ManifoldImmersion.exists_embedded_avoidance_relative_neighborhood_of_isClosed_range
      f o hf ho hclosed hself hobs isCompact_Icc
      (show IsClosed C from isClosed_closedBall.union isClosed_closedBall) hBC hfi hfd hclean
  refine ⟨g, hg, ?_, ?_, hge, hgd, ?_⟩
  · filter_upwards [h0C, hfa] with t ht he
    exact (hrel.fst_eq_snd ht).symm.trans he
  · filter_upwards [h1C, hfb] with t ht he
    exact (hrel.fst_eq_snd ht).symm.trans he
  · intro t ht hto
    have htB : t ∉ ({0, 1} : Set ℝ) := by
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨ne_of_gt ht.1, ne_of_lt ht.2⟩
    exact havoid t ⟨⟨ht.1.le, ht.2.le⟩, htB⟩ hto

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
