import Wikipedia.HopfProblem.TriangleUniformizationGluingEdgesCurves
import Wikipedia.HopfProblem.TriangleUniformizationGluingEdgesAmbient
import Wikipedia.HopfProblem.TriangleUniformizationGluingEdgesTopology
import Wikipedia.HopfProblem.TriangleUniformizationGluingRemovableUnions

/-!
# Holomorphic gluing across the actual triangle edges

Each closed edge portion is contained in a proved removable analytic
curve.  The actual holomorphic triangle action transports this property
to every translated edge.  Local finiteness belongs to the edge portions
contained in the closed tiles, not to the extended geodesics.

Consequently, a continuous function on the upper half-plane that is
holomorphic on every open triangle is holomorphic on the full domain.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology ContDiff Manifold

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

open SpecialPeriods SpecialPeriods.Triangle

/-- Each of the six simple curves containing a folded base edge is
continuously removable on the complex upper half-plane. -/
theorem continuousRemovable_foldedEdgeComplexCarrier (b : Bool) (k : Fin 3) :
    ContinuousRemovable upperHalfPlaneSet (foldedEdgeComplexCarrier b k) := by
  cases b <;> fin_cases k
  · exact continuousRemovable_verticalLine stripLeft
  · exact continuousRemovable_verticalLine (-(1 / 2))
  · change ContinuousRemovable upperHalfPlaneSet {z : ℂ | ‖z + 1‖ = 1}
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, sub_neg_eq_add] using
      continuousRemovable_unitCircle (-1)
  · exact continuousRemovable_verticalLine stripRight
  · exact continuousRemovable_verticalLine (-(1 / 2))
  · change ContinuousRemovable upperHalfPlaneSet {z : ℂ | ‖z‖ = 1}
    simpa only [Complex.ofReal_zero, sub_zero] using
      continuousRemovable_unitCircle 0

/-- The actual folded base edge inherits removability from its full curve. -/
theorem continuousRemovable_foldedHalfEdge (b : Bool) (k : Fin 3) :
    ContinuousRemovable upperHalfPlaneSet
      (((↑) : ℍ → ℂ) '' (halfFold b '' halfFordEdge k)) :=
  (continuousRemovable_foldedEdgeComplexCarrier b k).mono_set
    (foldedEdgeComplex_subset_carrier b k)

/-- Every actual translated closed edge portion is continuously removable. -/
theorem continuousRemovable_triangleEdgeComplex (j : TriangleEdgeIndex) :
    ContinuousRemovable upperHalfPlaneSet (triangleEdgeComplex j) := by
  rcases j with ⟨⟨g, b⟩, k⟩
  have hsource : upperHalfPlaneSet ⊆ (triangleAmbientMap g).source := by
    rw [triangleAmbientMap_source]
  have hsubset : ((↑) : ℍ → ℂ) '' (halfFold b '' halfFordEdge k) ⊆
      upperHalfPlaneSet := by
    rintro z ⟨w, _, rfl⟩
    exact w.im_pos
  have h := (continuousRemovable_foldedHalfEdge b k).image
    (e := triangleAmbientMap g) hsource hsubset
    (triangleAmbientMap_differentiableOn g) (triangleAmbientMap_symm_differentiableOn g)
  simpa only [triangleAmbientMap_image_upperHalfPlaneSet, triangleAmbientMap_image_coe,
    triangleEdgeComplex, halfTriangleEdge_eq] using h

/-- The union of the actual edge portions is removable.  Relative
closedness and local finiteness are proved for these pieces themselves. -/
theorem continuousRemovable_triangleEdges :
    ContinuousRemovable upperHalfPlaneSet
      (⋃ j : TriangleEdgeIndex, triangleEdgeComplex j) :=
  continuousRemovable_iUnion_of_locallyFinite isOpen_upperHalfPlaneSet
    triangleEdgeComplex continuousRemovable_triangleEdgeComplex
    triangleEdgeComplex_relative_compl_isOpen triangleEdgeComplex_locallyFinite

/-- Continuous complex functions holomorphic on the actual open tiles
are holomorphic across all their edges and vertices. -/
theorem differentiableOn_of_continuousOn_halfTriangleOpenTiles {f : ℂ → ℂ}
    (hf : ContinuousOn f upperHalfPlaneSet)
    (hd : ∀ i : TriangleGroup × Bool,
      DifferentiableOn ℂ f (((↑) : ℍ → ℂ) '' halfTriangleOpenTile i)) :
    DifferentiableOn ℂ f upperHalfPlaneSet := by
  apply continuousRemovable_triangleEdges upperHalfPlaneSet
    isOpen_upperHalfPlaneSet Subset.rfl f hf
  intro z hz
  have htile : z ∈ ⋃ i : TriangleGroup × Bool,
      ((↑) : ℍ → ℂ) '' halfTriangleOpenTile i := by
    by_contra hnot
    exact hz.2 (triangleEdgeComplex_cover_openTile_complement ⟨hz.1, hnot⟩)
  obtain ⟨i, hi⟩ := mem_iUnion.mp htile
  exact (hd i).differentiableAt
    ((UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ (halfTriangleOpenTile_isOpen i)).mem_nhds hi)

/-- A continuous map on the genuine upper-half-plane manifold that is
holomorphic on every open triangle is globally holomorphic. -/
theorem contMDiff_of_continuous_of_halfTriangleOpenTiles {f : ℍ → ℂ}
    (hf : Continuous f)
    (hd : ∀ i : TriangleGroup × Bool,
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω f (halfTriangleOpenTile i)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  have hfc : ContinuousOn (f ∘ UpperHalfPlane.ofComplex) upperHalfPlaneSet := by
    intro z hz
    exact (hf.continuousAt.comp
      (UpperHalfPlane.contMDiffAt_ofComplex (n := ω) hz).continuousAt).continuousWithinAt
  have hfd : ∀ i : TriangleGroup × Bool,
      DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex)
        (((↑) : ℍ → ℂ) '' halfTriangleOpenTile i) := by
    intro i z hz
    rcases hz with ⟨w, hw, rfl⟩
    have ht : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f w :=
      (hd i w hw).contMDiffAt ((halfTriangleOpenTile_isOpen i).mem_nhds hw)
    exact ((UpperHalfPlane.contMDiffAt_iff.mp ht).differentiableAt
      (by simp)).differentiableWithinAt
  have hglobal := differentiableOn_of_continuousOn_halfTriangleOpenTiles hfc hfd
  intro z
  apply UpperHalfPlane.contMDiffAt_iff.mpr
  exact (hglobal.analyticOnNhd isOpen_upperHalfPlaneSet z z.im_pos).contDiffAt

end Wikipedia.HopfProblem.TriangleUniformizationGluing
