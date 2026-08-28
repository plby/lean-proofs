import Wikipedia.SmoothSixDPoincare.SmoothCurveEndpointGerms
import Wikipedia.SmoothSixDPoincare.CurveEndpointNeighborhood
import Wikipedia.SmoothSixDPoincare.RelativeCurveAvoidance

/-!
# Embedded connecting arcs preserving prescribed endpoint germs

The supplied germs need only have injective native derivative at the endpoints
and distinct endpoint values. A continuous path between them gives an embedded
immersive connecting arc, avoiding a finite set in its interior, with both germs
unchanged. The initially clean endpoint neighborhoods are constructed.
-/

noncomputable section

open Set Function Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- An embedded immersive connecting arc can retain both prescribed immersive endpoint germs. -/
theorem exists_embedded_arc_with_endpoint_germs (a b : C(ℝ, N))
    (ha : ContMDiff 𝓘(ℝ, ℝ) J ∞ a) (hb : ContMDiff 𝓘(ℝ, ℝ) J ∞ b)
    (hia : Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Injective (mfderiv 𝓘(ℝ, ℝ) J b 1))
    (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1) (hdim : 3 ≤ Module.finrank ℝ G)
    {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
      (f =ᶠ[𝓝 (0 : ℝ)] a) ∧ (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ S) := by
  obtain ⟨g, hg, hga, hgb⟩ := exists_smooth_curve_with_endpoint_germs a b ha hb γ
  have hga0 : g =ᶠ[𝓝 (0 : ℝ)] a := by
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num)] with t ht
    change t < 1 / 8 at ht
    exact hga ht.le
  have hgb1 : g =ᶠ[𝓝 (1 : ℝ)] b := by
    filter_upwards [Ioi_mem_nhds (show (7 / 8 : ℝ) < 1 by norm_num)] with t ht
    change 7 / 8 < t at ht
    exact hgb ht.le
  have hgxy : g 0 ≠ g 1 := by
    rw [hga0.eq_of_nhds, hgb1.eq_of_nhds]
    exact hxy
  have hig0 : Injective (mfderiv 𝓘(ℝ, ℝ) J g 0) := by
    rw [hga0.mfderiv_eq]
    exact hia
  have hig1 : Injective (mfderiv 𝓘(ℝ, ℝ) J g 1) := by
    rw [hgb1.mfderiv_eq]
    exact hib
  obtain ⟨C, hC, hBC, hinjC, hiC, hclean⟩ :=
    ManifoldImmersion.exists_clean_curve_endpoint_neighborhood hg hgxy hig0 hig1 hS
  obtain ⟨f, hf, hrel, hemb, hi, havoid⟩ :=
    ManifoldImmersion.exists_relative_curve_avoiding_finite g hg hdim hS
      (isCompact_Icc (a := (0 : ℝ)) (b := 1)) hC.isClosed hBC
      (hinjC.mono inter_subset_right) (fun t ht => hiC t ht.2)
      (fun t ht => hclean t ht.2)
  have hfg (t : ℝ) (ht : t ∈ ({0, 1} : Set ℝ)) : f =ᶠ[𝓝 t] g := by
    filter_upwards [isOpen_interior.mem_nhds (hBC ht)] with s hs
    exact (hrel.fst_eq_snd (interior_subset hs)).symm
  refine ⟨f, hf, (hfg 0 (by simp)).trans hga0, (hfg 1 (by simp)).trans hgb1, hemb, hi, ?_⟩
  intro t ht
  apply havoid t ⟨⟨ht.1.le, ht.2.le⟩, ?_⟩
  intro htB
  rcases htB with ht0 | ht1
  · exact ht.1.ne' ht0
  · exact ht.2.ne ht1

end Wikipedia.SmoothSixDPoincare
