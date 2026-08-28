import Wikipedia.NoExoticSixSphere.FramedTubularNeighborhood
import Wikipedia.NoExoticSixSphere.SmoothCompressedProductTube

/-!
# An unrestricted smooth product tube for a framed embedding

The radius and partial diffeomorphism are obtained from the actual tubular
neighborhood. The full product is the source, and the forward formula retains
the given smooth normal frame explicitly.
-/

open scoped Manifold ContDiff
open Set Topology

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [Nonempty M] [CompactSpace M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)

theorem exists_smoothFramedTube :
    ∃ r : ℝ, 0 < r ∧
      ∃ Φ : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
          (M × e.NormalModel) (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞,
        Φ.source = univ ∧
        (∀ p, Φ p = e.toFun p.1 +
          a.ambient p.1 (OpenPartialHomeomorph.univBall (0 : e.NormalModel) r p.2)) ∧
        (∀ x, Φ (x, 0) = e.toFun x) ∧ range e.toFun ⊆ Φ.target := by
  obtain ⟨Ψ, hzero, hformula, _⟩ := e.exists_framedTubularNeighborhood a
  obtain ⟨r, hr, hsource⟩ := exists_uniform_closedProductTube Ψ.open_source hzero
  let Φ := CompressedProductTube.smoothTube Ψ r hr
  have hs : Φ.source = univ := CompressedProductTube.smoothTube_source Ψ r hr hsource
  have hz (x : M) : Φ (x, 0) = e.toFun x := by
    rw [CompressedProductTube.smoothTube_zero, hformula, map_zero, add_zero]
  refine ⟨r, hr, Φ, hs, ?_, hz, ?_⟩
  · intro p
    exact hformula _
  · rintro _ ⟨x, rfl⟩
    rw [← hz]
    exact Φ.map_source' (by rw [hs]; trivial)

end NoExoticSixSphere.EuclideanEmbedding
