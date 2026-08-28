import Wikipedia.SmoothSixDPoincare.OpenGluingManifold

/-!
# The original gluing patches are native smooth local coordinates

The open embeddings have smooth inverses on their actual ranges. Their
partial diffeomorphisms retain the original point maps and entire sources.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.OpenGluing

section LiftedAtlas

variable {E H X Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [Nonempty H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [Nonempty X]
  [TopologicalSpace Z] [ChartedSpace H Z] [IsManifold I ∞ Z]

omit [IsManifold I ∞ Z] in
theorem contMDiffOn_inverse_of_lifted_atlas {i : X → Z} (hi : IsOpenEmbedding i)
    (hatlas : ∀ c ∈ atlas H X,
      c.lift_openEmbedding hi ∈ IsManifold.maximalAtlas I ∞ Z) :
    ContMDiffOn I I ∞ hi.toOpenPartialHomeomorph.symm (range i) := by
  rintro z ⟨x, rfl⟩
  let c := chartAt H x
  let C := c.lift_openEmbedding hi
  have hc := IsManifold.chart_mem_maximalAtlas (I := I) (n := (∞ : ℕ∞ω)) x
  have hC := hatlas c (chart_mem_atlas H x)
  have hs : ContMDiffOn I I ∞ (c.symm ∘ C) C.source :=
    (contMDiffOn_symm_of_mem_maximalAtlas hc).comp
      (contMDiffOn_of_mem_maximalAtlas hC) C.mapsTo
  have hinv : ContMDiffOn I I ∞ hi.toOpenPartialHomeomorph.symm C.source := by
    apply hs.congr
    rintro w ⟨y, hy, rfl⟩
    change hi.toOpenPartialHomeomorph.symm (i y) = c.symm (C (i y))
    rw [hi.toOpenPartialHomeomorph_left_inv,
      OpenPartialHomeomorph.lift_openEmbedding_apply, c.left_inv hy]
  exact (hinv.contMDiffAt (C.open_source.mem_nhds
    ⟨x, mem_chart_source H x, rfl⟩)).contMDiffWithinAt

end LiftedAtlas

variable {E H X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [Nonempty H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y]
  (e : PartialDiffeomorph I I X Y ∞)

def leftPartialDiffeomorph [Nonempty X] :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    PartialDiffeomorph I I X (Space e.toOpenPartialHomeomorph) ∞ := by
  let _ := chartedSpace (H := H) e.toOpenPartialHomeomorph
  let _ := isManifold e
  let hi := left_isOpenEmbedding e.toOpenPartialHomeomorph
  refine {
    toPartialEquiv := hi.toOpenPartialHomeomorph.toPartialEquiv
    open_source := isOpen_univ
    open_target := hi.toOpenPartialHomeomorph.open_target
    contMDiffOn_toFun := (contMDiff_left e).contMDiffOn
    contMDiffOn_invFun := ?_ }
  change ContMDiffOn I I ∞ hi.toOpenPartialHomeomorph.symm
    hi.toOpenPartialHomeomorph.target
  rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact contMDiffOn_inverse_of_lifted_atlas (I := I) hi fun c hc =>
    IsManifold.subset_maximalAtlas (left_chart_mem_atlas e.toOpenPartialHomeomorph c hc)

def rightPartialDiffeomorph [Nonempty Y] :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    PartialDiffeomorph I I Y (Space e.toOpenPartialHomeomorph) ∞ := by
  let _ := chartedSpace (H := H) e.toOpenPartialHomeomorph
  let _ := isManifold e
  let hi := right_isOpenEmbedding e.toOpenPartialHomeomorph
  refine {
    toPartialEquiv := hi.toOpenPartialHomeomorph.toPartialEquiv
    open_source := isOpen_univ
    open_target := hi.toOpenPartialHomeomorph.open_target
    contMDiffOn_toFun := (contMDiff_right e).contMDiffOn
    contMDiffOn_invFun := ?_ }
  change ContMDiffOn I I ∞ hi.toOpenPartialHomeomorph.symm
    hi.toOpenPartialHomeomorph.target
  rw [IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact contMDiffOn_inverse_of_lifted_atlas (I := I) hi fun c hc =>
    IsManifold.subset_maximalAtlas (right_chart_mem_atlas e.toOpenPartialHomeomorph c hc)

theorem leftPartialDiffeomorph_apply [Nonempty X] (x : X) :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    leftPartialDiffeomorph e x = left e.toOpenPartialHomeomorph x := rfl

theorem rightPartialDiffeomorph_apply [Nonempty Y] (y : Y) :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    rightPartialDiffeomorph e y = right e.toOpenPartialHomeomorph y := rfl

theorem leftPartialDiffeomorph_symm_left [Nonempty X] (x : X) :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    (leftPartialDiffeomorph e).symm (left e.toOpenPartialHomeomorph x) = x := by
  exact (leftPartialDiffeomorph e).left_inv (mem_univ x)

theorem rightPartialDiffeomorph_symm_right [Nonempty Y] (y : Y) :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    (rightPartialDiffeomorph e).symm (right e.toOpenPartialHomeomorph y) = y := by
  exact (rightPartialDiffeomorph e).left_inv (mem_univ y)

theorem leftPartialDiffeomorph_source [Nonempty X] :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    (leftPartialDiffeomorph e).source = univ := rfl

theorem rightPartialDiffeomorph_source [Nonempty Y] :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    (rightPartialDiffeomorph e).source = univ := rfl

theorem leftPartialDiffeomorph_target [Nonempty X] :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    (leftPartialDiffeomorph e).target = range (left e.toOpenPartialHomeomorph) := by
  exact IsOpenEmbedding.toOpenPartialHomeomorph_target
    (left e.toOpenPartialHomeomorph) (left_isOpenEmbedding e.toOpenPartialHomeomorph)

theorem rightPartialDiffeomorph_target [Nonempty Y] :
    letI := chartedSpace (H := H) e.toOpenPartialHomeomorph
    (rightPartialDiffeomorph e).target = range (right e.toOpenPartialHomeomorph) := by
  exact IsOpenEmbedding.toOpenPartialHomeomorph_target
    (right e.toOpenPartialHomeomorph) (right_isOpenEmbedding e.toOpenPartialHomeomorph)

end Wikipedia.SmoothSixDPoincare.OpenGluing
