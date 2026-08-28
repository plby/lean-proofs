import Wikipedia.NoExoticSixSphere.ConvexLocalInjectivity
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Local injectivity in genuine convex boundary models

The argument stays within the model's convex range. It pulls a local
mean-value estimate back through the actual source chart and does not
replace a boundary manifold by an assumed boundaryless extension.
-/

noncomputable section

open Function Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_open_injOn_of_convex_model {f : M → F} (x : M)
    (hI : Convex ℝ (range I)) (hf : ContMDiffAt I 𝓘(ℝ, F) 1 f x)
    (L : E ≃L[ℝ] F) (hL : mvfderiv I f x = L.toContinuousLinearMap) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ InjOn f U := by
  let c := extChartAt I x
  let g := writtenInExtChartAt I 𝓘(ℝ, F) x f
  have hg : ContDiffWithinAt ℝ 1 g (range I) (c x) := (contMDiffAt_iff.mp hf).2
  have hx : c x ∈ range I :=
    extChartAt_target_subset_range x (mem_extChartAt_target x)
  have hD := (hf.mdifferentiableAt (by norm_num)).mvfderiv
  have hGL : fderivWithin ℝ g (range I) (c x) = L.toContinuousLinearMap := hD.symm.trans hL
  obtain ⟨t, ht, hit⟩ := exists_injOn_nhdsWithin_of_convex_contDiffWithinAt
    hI I.uniqueDiffOn hx hg L hGL
  have hpre : c ⁻¹' t ∈ 𝓝 x := by
    have hm : t ∈ Filter.map c (𝓝 x) := by
      rwa [map_extChartAt_nhds]
    exact hm
  have hnear : c.source ∩ c ⁻¹' t ∈ 𝓝 x := inter_mem (extChartAt_source_mem_nhds x) hpre
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnear
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy z hz he
  have hyc : y ∈ c.source := (hUsub hy).1
  have hzc : z ∈ c.source := (hUsub hz).1
  have hgy : g (c y) = f y := by
    change f (c.symm (c y)) = f y
    rw [c.left_inv hyc]
  have hgz : g (c z) = f z := by
    change f (c.symm (c z)) = f z
    rw [c.left_inv hzc]
  have hcoord := hit (hUsub hy).2 (hUsub hz).2 (hgy.trans (he.trans hgz.symm))
  exact c.injOn hyc hzc hcoord

end NoExoticSixSphere
