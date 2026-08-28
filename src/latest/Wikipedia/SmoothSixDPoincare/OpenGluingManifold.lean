import Wikipedia.SmoothSixDPoincare.OpenGluingCharts
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Smooth structure on the actual open gluing

A genuine partial diffeomorphism gives compatible lifted atlases on the
quotient. Both original patch inclusions are smooth in this structure.
No Hausdorff or compactness conclusion is inferred from open gluing alone.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.OpenGluing

variable {E H X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [Nonempty H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H Y]

private def atlasPartialDiffeomorph (c : OpenPartialHomeomorph X H)
    (hc : c ∈ IsManifold.maximalAtlas I ∞ X) : PartialDiffeomorph I I X H ∞ where
  toPartialEquiv := c.toPartialEquiv
  open_source := c.open_source
  open_target := c.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hc
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hc

omit [Nonempty H] in
private theorem model_partial_mem (p : PartialDiffeomorph I I H H ∞) :
    p.toOpenPartialHomeomorph ∈ contDiffGroupoid ∞ I := by
  have hp := p.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    p.contMDiffOn p.symm.contMDiffOn
  have h := hp (OpenPartialHomeomorph.refl H) (by simp)
  simpa only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans] using h.2

variable [IsManifold I ∞ X] [IsManifold I ∞ Y]

omit [Nonempty H] in
theorem chart_transition_mem (e : PartialDiffeomorph I I X Y ∞)
    (c : OpenPartialHomeomorph X H) (d : OpenPartialHomeomorph Y H)
    (hc : c ∈ atlas H X) (hd : d ∈ atlas H Y) :
    (c.symm.trans e.toOpenPartialHomeomorph).trans d ∈ contDiffGroupoid ∞ I := by
  let C := atlasPartialDiffeomorph (I := I) c (IsManifold.subset_maximalAtlas hc)
  let D := atlasPartialDiffeomorph (I := I) d (IsManifold.subset_maximalAtlas hd)
  exact model_partial_mem ((C.symm.trans e).trans D)

/-- The prescribed smooth transition makes the quotient a native smooth manifold. -/
theorem isManifold (e : PartialDiffeomorph I I X Y ∞) :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    IsManifold I ∞ (Space e.toOpenPartialHomeomorph) := by
  let _ := chartedSpace (H := H) e.toOpenPartialHomeomorph
  refine { compatible := ?_ }
  intro a b ha hb
  change a ∈ gluedAtlas e.toOpenPartialHomeomorph at ha
  change b ∈ gluedAtlas e.toOpenPartialHomeomorph at hb
  rcases ha with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · rcases hb with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
      exact (contDiffGroupoid ∞ I).compatible hc hd
    · exact (contDiffGroupoid ∞ I).mem_of_eqOnSource (chart_transition_mem e c d hc hd)
        (left_right_transition e.toOpenPartialHomeomorph c d)
  · rcases hb with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · exact (contDiffGroupoid ∞ I).mem_of_eqOnSource (chart_transition_mem e.symm c d hc hd)
        (right_left_transition e.toOpenPartialHomeomorph c d)
    · rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
      exact (contDiffGroupoid ∞ I).compatible hc hd

theorem contMDiff_left (e : PartialDiffeomorph I I X Y ∞) :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    ContMDiff I I ∞ (left e.toOpenPartialHomeomorph) := by
  let _ := chartedSpace (H := H) e.toOpenPartialHomeomorph
  let _ := isManifold e
  intro x
  let c := chartAt H x
  let C := c.lift_openEmbedding (left_isOpenEmbedding e.toOpenPartialHomeomorph)
  have hC : C ∈ IsManifold.maximalAtlas I ∞ (Space e.toOpenPartialHomeomorph) :=
    IsManifold.subset_maximalAtlas
      (left_chart_mem_atlas e.toOpenPartialHomeomorph c (chart_mem_atlas H x))
  have hs : ContMDiffOn I I ∞ (C.symm ∘ c) c.source :=
    (contMDiffOn_symm_of_mem_maximalAtlas hC).comp contMDiffOn_chart c.mapsTo
  have hleft : ContMDiffOn I I ∞ (left e.toOpenPartialHomeomorph) c.source := by
    apply hs.congr
    intro y hy
    change left e.toOpenPartialHomeomorph y = left e.toOpenPartialHomeomorph (c.symm (c y))
    rw [c.left_inv hy]
  exact hleft.contMDiffAt (c.open_source.mem_nhds (mem_chart_source H x))

theorem contMDiff_right (e : PartialDiffeomorph I I X Y ∞) :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    ContMDiff I I ∞ (right e.toOpenPartialHomeomorph) := by
  let _ := chartedSpace (H := H) e.toOpenPartialHomeomorph
  let _ := isManifold e
  intro y
  let d := chartAt H y
  let D := d.lift_openEmbedding (right_isOpenEmbedding e.toOpenPartialHomeomorph)
  have hD : D ∈ IsManifold.maximalAtlas I ∞ (Space e.toOpenPartialHomeomorph) :=
    IsManifold.subset_maximalAtlas
      (right_chart_mem_atlas e.toOpenPartialHomeomorph d (chart_mem_atlas H y))
  have hs : ContMDiffOn I I ∞ (D.symm ∘ d) d.source :=
    (contMDiffOn_symm_of_mem_maximalAtlas hD).comp contMDiffOn_chart d.mapsTo
  have hright : ContMDiffOn I I ∞ (right e.toOpenPartialHomeomorph) d.source := by
    apply hs.congr
    intro z hz
    change right e.toOpenPartialHomeomorph z = right e.toOpenPartialHomeomorph (d.symm (d z))
    rw [d.left_inv hz]
  exact hright.contMDiffAt (d.open_source.mem_nhds (mem_chart_source H y))

end Wikipedia.SmoothSixDPoincare.OpenGluing
