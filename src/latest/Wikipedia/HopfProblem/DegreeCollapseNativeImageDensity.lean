import Wikipedia.HopfProblem.DegreeCollapseNativeMiddleDiskCrossing
import Wikipedia.SmoothSixDPoincare.ManifoldImageDimension

/-!
# The complement of a lower-dimensional native smooth image is dense

The dimension estimate is applied in each actual target chart, restricted
to the whole preimage of that chart. Thus the conclusion concerns the full
native image, not a selected compact piece or an auxiliary embedding.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V E H H' Y M : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ V H'} {J : ModelWithCorners ℝ E H} [J.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I ∞ Y] [LindelofSpace Y]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M]

theorem dense_compl_native_smooth_image {g : Y → M} (hg : ContMDiff I J ∞ g)
    (hdim : Module.finrank ℝ V < Module.finrank ℝ E) : Dense (range g)ᶜ := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  obtain ⟨x, hxU⟩ := hUne
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) x
  have hxc : x ∈ c.source := mem_extChartAt_source x
  let W : Set Y := g ⁻¹' c.source
  have hW : IsOpen W := c.open_source.preimage hg.continuous
  have hcg : ContMDiffOn I 𝓘(ℝ, E) ∞ (c ∘ g) W :=
    c.contMDiffOn_toFun.comp hg.contMDiffOn (fun _ hy => hy)
  have hdense := GeneralPosition.dense_compl_manifold_image hW hcg hdim
  have hcoordOpen : IsOpen (c '' (U ∩ c.source)) :=
    c.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (hU.inter c.open_source) inter_subset_right
  obtain ⟨z, hzavoid, y, hy, hyz⟩ :=
    hdense.exists_mem_open hcoordOpen ⟨c x, x, ⟨hxU, hxc⟩, rfl⟩
  refine ⟨y, hy.1, ?_⟩
  rintro ⟨q, hq⟩
  apply hzavoid
  refine ⟨q, ?_, ?_⟩
  · change g q ∈ c.source
    rw [hq]
    exact hy.2
  · change c (g q) = z
    rw [hq]
    exact hyz

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
