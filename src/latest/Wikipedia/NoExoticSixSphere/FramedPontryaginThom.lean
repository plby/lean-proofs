import Wikipedia.NoExoticSixSphere.SmoothFramedCollapse

/-!
# The actual collapse map of a smoothly framed Euclidean embedding

A uniform product disk in the tubular neighborhood is reparametrized by
the entire normal model. Collapsing its complement gives a continuous map
between one-point compactifications, with exactly the embedded manifold as
the fiber over zero. This constructs the map, not the bordism correspondence
or its stable homotopy class computation.
-/

open scoped Manifold ContDiff
open Set Topology

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [Nonempty M] [CompactSpace M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)

include a in
theorem exists_framedOpenTube :
    ∃ τ : M × e.NormalModel → EuclideanSpace ℝ (Fin e.ambientDimension),
      IsOpenEmbedding τ ∧ ∀ x, τ (x, 0) = e.toFun x := by
  obtain ⟨Φ, hzero, hformula, _⟩ := e.exists_framedTubularNeighborhood a
  obtain ⟨r, hr, hsource⟩ := exists_uniform_closedProductTube Φ.open_source hzero
  refine ⟨CompressedProductTube.map Φ.toOpenPartialHomeomorph r,
    CompressedProductTube.isOpenEmbedding_map Φ.toOpenPartialHomeomorph r hr hsource, ?_⟩
  intro x
  rw [CompressedProductTube.map_zero]
  change Φ (x, 0) = e.toFun x
  rw [hformula, map_zero, add_zero]

include a in
theorem exists_framedCollapse :
    ∃ F : C(OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension)), OnePoint e.NormalModel),
      F OnePoint.infty = OnePoint.infty ∧
      ∀ y, F y = ((0 : e.NormalModel) : OnePoint e.NormalModel) ↔
        ∃ x, (e.toFun x : OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension))) = y := by
  let d := e.framedCollapseData a
  exact ⟨d.map, d.map_infty, d.zero_fiber⟩

end NoExoticSixSphere.EuclideanEmbedding
