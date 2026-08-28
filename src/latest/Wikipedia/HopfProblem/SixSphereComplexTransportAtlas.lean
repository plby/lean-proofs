import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Transporting an actual manifold atlas along a homeomorphism

The target keeps its original topology. Each transported chart is the old
chart composed with the inverse homeomorphism. Its transition maps are
literally the original transition maps. This construction proves no
existence statement about homeomorphisms or diffeomorphisms.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ManifoldAtlasTransport

variable {H M N : Type*} [TopologicalSpace H] [Nonempty H]
  [TopologicalSpace M] [TopologicalSpace N] [ChartedSpace H M]

/-- Push the original charts forward, without changing the target topology. -/
@[instance_reducible] def chartedSpace (h : M ≃ₜ N) : ChartedSpace H N where
  atlas := (fun e : OpenPartialHomeomorph M H =>
    e.lift_openEmbedding h.isOpenEmbedding) '' atlas H M
  chartAt y := (chartAt H (h.symm y)).lift_openEmbedding h.isOpenEmbedding
  mem_chart_source y :=
    ⟨h.symm y, mem_chart_source H (h.symm y), h.apply_symm_apply y⟩
  chart_mem_atlas y :=
    ⟨chartAt H (h.symm y), chart_mem_atlas H (h.symm y), rfl⟩

theorem mem_atlas (h : M ≃ₜ N) {e : OpenPartialHomeomorph M H}
    (he : e ∈ atlas H M) :
    letI := chartedSpace (H := H) h
    e.lift_openEmbedding h.isOpenEmbedding ∈ atlas H N :=
  ⟨e, he, rfl⟩

omit [ChartedSpace H M] in
/-- On every point, not just the chart domain, the transported coordinate
is the original coordinate after the actual inverse homeomorphism. -/
theorem chart_apply (h : M ≃ₜ N) (e : OpenPartialHomeomorph M H) (y : N) :
    e.lift_openEmbedding h.isOpenEmbedding y = e (h.symm y) := by
  have he := e.lift_openEmbedding_apply h.isOpenEmbedding (x := h.symm y)
  simpa only [h.apply_symm_apply] using he

omit [ChartedSpace H M] in
/-- Transport does not alter any change of coordinates. -/
theorem transition_eq (h : M ≃ₜ N) (e e' : OpenPartialHomeomorph M H) :
    (e.lift_openEmbedding h.isOpenEmbedding).symm.trans
        (e'.lift_openEmbedding h.isOpenEmbedding) = e.symm.trans e' :=
  e.lift_openEmbedding_trans e' h.isOpenEmbedding

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (I : ModelWithCorners 𝕜 E H) (n : ℕ∞ω)

/-- The transported atlas has exactly the original differentiability class. -/
theorem isManifold (h : M ≃ₜ N) [IsManifold I n M] :
    letI := chartedSpace (H := H) h
    IsManifold I n N := by
  let := chartedSpace (H := H) h
  refine { compatible := ?_ }
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  rw [transition_eq]
  exact (contDiffGroupoid n I).compatible he he'

theorem contMDiff (h : M ≃ₜ N) [IsManifold I n M] :
    letI := chartedSpace (H := H) h
    ContMDiff I I n h := by
  let := chartedSpace (H := H) h
  let := isManifold I n h
  intro x
  let e := chartAt H x
  have he : e ∈ IsManifold.maximalAtlas I n M :=
    IsManifold.chart_mem_maximalAtlas x
  have he' : e.lift_openEmbedding h.isOpenEmbedding ∈
      IsManifold.maximalAtlas I n N :=
    IsManifold.subset_maximalAtlas (mem_atlas h (chart_mem_atlas H x))
  have hx : x ∈ e.source := mem_chart_source H x
  have hx' : e x ∈ (e.lift_openEmbedding h.isOpenEmbedding).target :=
    e.map_source hx
  have hc := (contMDiffAt_symm_of_mem_maximalAtlas he' hx').comp x
    (contMDiffAt_of_mem_maximalAtlas he hx)
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, OpenPartialHomeomorph.lift_openEmbedding_symm,
    e.left_inv hy]

theorem contMDiff_symm (h : M ≃ₜ N) [IsManifold I n M] :
    letI := chartedSpace (H := H) h
    ContMDiff I I n h.symm := by
  let := chartedSpace (H := H) h
  let := isManifold I n h
  intro y
  let e := chartAt H (h.symm y)
  let e' := e.lift_openEmbedding h.isOpenEmbedding
  have he : e ∈ IsManifold.maximalAtlas I n M :=
    IsManifold.chart_mem_maximalAtlas (h.symm y)
  have he' : e' ∈ IsManifold.maximalAtlas I n N :=
    IsManifold.subset_maximalAtlas (mem_atlas h (chart_mem_atlas H (h.symm y)))
  have hy : y ∈ e'.source :=
    ⟨h.symm y, mem_chart_source H (h.symm y), h.apply_symm_apply y⟩
  have hy' : e' y ∈ e.target := e'.map_source hy
  have hc := (contMDiffAt_symm_of_mem_maximalAtlas he hy').comp y
    (contMDiffAt_of_mem_maximalAtlas he' hy)
  apply hc.congr_of_eventuallyEq
  filter_upwards [e'.open_source.mem_nhds hy] with z hz
  have heq := congrArg h.symm (e'.left_inv hz)
  simpa only [e', OpenPartialHomeomorph.lift_openEmbedding_symm,
    Function.comp_apply, h.symm_apply_apply] using heq.symm

/-- The supplied homeomorphism is a genuine diffeomorphism for the
transported atlas; its underlying function is unchanged. -/
def diffeomorph (h : M ≃ₜ N) [IsManifold I n M] :
    letI := chartedSpace (H := H) h
    M ≃ₘ^n⟮I, I⟯ N := by
  letI := chartedSpace (H := H) h
  exact { h.toEquiv with
    contMDiff_toFun := contMDiff I n h
    contMDiff_invFun := contMDiff_symm I n h }

@[simp] theorem diffeomorph_apply (h : M ≃ₜ N) [IsManifold I n M] (x : M) :
    letI := chartedSpace (H := H) h
    diffeomorph I n h x = h x := rfl

@[simp] theorem diffeomorph_symm_apply (h : M ≃ₜ N) [IsManifold I n M] (y : N) :
    letI := chartedSpace (H := H) h
    (diffeomorph I n h).symm y = h.symm y := rfl

end Wikipedia.HopfProblem.ManifoldAtlasTransport
