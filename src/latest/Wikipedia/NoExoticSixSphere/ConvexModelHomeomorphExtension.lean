import Wikipedia.NoExoticSixSphere.ConvexLocalHomeomorphExtension
import Wikipedia.NoExoticSixSphere.ConvexModelLocalInjectivity

/-!
# A local ambient homeomorphism in actual manifold coordinates

A map with invertible differential agrees locally with an ambient
homeomorphism after its actual extended source chart, including at boundary
points. The source chart range is retained; no ambient-open image is assumed.
-/

noncomputable section

open Function Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_homeomorph_chart_of_convex_model {f : M → F} (x : M)
    (hI : Convex ℝ (range I)) (hf : ContMDiffAt I 𝓘(ℝ, F) 1 f x)
    (L : E ≃L[ℝ] F) (hL : mvfderiv I f x = L.toContinuousLinearMap) :
    ∃ (U : Set M) (G : E ≃ₜ F), IsOpen U ∧ x ∈ U ∧
      U ⊆ (extChartAt I x).source ∧ EqOn f (G ∘ extChartAt I x) U := by
  let c := extChartAt I x
  let g := writtenInExtChartAt I 𝓘(ℝ, F) x f
  have hg : ContDiffWithinAt ℝ 1 g (range I) (c x) := (contMDiffAt_iff.mp hf).2
  have hx : c x ∈ range I := extChartAt_target_subset_range x (mem_extChartAt_target x)
  have hD := (hf.mdifferentiableAt (by norm_num)).mvfderiv
  have hGL : fderivWithin ℝ g (range I) (c x) = L.toContinuousLinearMap := hD.symm.trans hL
  obtain ⟨t, G, ht, he⟩ := exists_homeomorph_nhdsWithin_of_convex_contDiffWithinAt
    hI I.uniqueDiffOn hx hg L hGL
  have hpre : c ⁻¹' t ∈ 𝓝 x := by
    have hm : t ∈ Filter.map c (𝓝 x) := by rwa [map_extChartAt_nhds]
    exact hm
  have hnear : c.source ∩ c ⁻¹' t ∈ 𝓝 x := inter_mem (extChartAt_source_mem_nhds x) hpre
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
  refine ⟨U, G, hU, hxU, fun _ hy ↦ (hUsub hy).1, ?_⟩
  intro y hy
  have hgy : g (c y) = f y := by
    change f (c.symm (c y)) = f y
    rw [c.left_inv (hUsub hy).1]
  exact hgy.symm.trans (he (hUsub hy).2)

end NoExoticSixSphere
