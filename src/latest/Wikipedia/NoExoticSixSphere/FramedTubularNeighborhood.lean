import Wikipedia.NoExoticSixSphere.FramedNormalCoordinates
import Wikipedia.NoExoticSixSphere.TubularNeighborhood

/-!
# A tubular neighborhood in global normal-frame coordinates

The product-to-normal-bundle diffeomorphism turns the actual tubular map
into the explicit formula `e(x) + A(x)v` on base times the normal model.
-/

open scoped Manifold ContDiff Bundle
open Set Bundle

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [Nonempty M] [CompactSpace M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)

theorem exists_framedTubularNeighborhood :
    ∃ Φ : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
        (M × e.NormalModel) (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞,
      (∀ x, (x, 0) ∈ Φ.source) ∧
      (∀ p, Φ p = e.toFun p.1 + a.ambient p.1 p.2) ∧
      range e.toFun ⊆ Φ.target := by
  obtain ⟨Ψ, hzero, hfun, _⟩ := e.exists_tubularNeighborhood
  let Φ := (e.framedNormalDiffeomorph a).toPartialDiffeomorph.trans Ψ
  have hs (x : M) : (x, 0) ∈ Φ.source := by
    change (x, 0) ∈ (univ : Set (M × e.NormalModel)) ∧
      e.framedNormalDiffeomorph a (x, 0) ∈ Ψ.source
    refine ⟨mem_univ _, ?_⟩
    rw [e.framedNormalDiffeomorph_zero]
    exact hzero ⟨x, rfl⟩
  have hf (p : M × e.NormalModel) : Φ p = e.toFun p.1 + a.ambient p.1 p.2 := by
    change Ψ (e.framedNormalDiffeomorph a p) = _
    rw [hfun]
    rfl
  refine ⟨Φ, hs, hf, ?_⟩
  rintro _ ⟨x, rfl⟩
  have h := Φ.map_source' (hs x)
  simpa only [hf, map_zero, add_zero] using h

end NoExoticSixSphere.EuclideanEmbedding
