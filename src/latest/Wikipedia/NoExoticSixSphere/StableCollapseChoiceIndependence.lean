import Wikipedia.NoExoticSixSphere.FramedCollapseHomotopyComparison
import Wikipedia.NoExoticSixSphere.StableSixSphereCollapse
import Wikipedia.NoExoticSixSphere.StableSixSphereRegularRepresentative

/-!
# The actual stable class is independent of collapse coordinates and tube choice

This is equality in the original direct limit, not merely equivalence of
vanishing predicates. The compact embedded manifold and its normal frame
are held fixed; no comparison of different embeddings or framings is asserted.
-/

noncomputable section

namespace NoExoticSixSphere.SphereMapSuspension

theorem reindex_homotopic {m n m' n' : ℕ} (hm : m = m') (hn : n = n')
    {f g : C(Sphere m, Sphere n)} (h : f.Homotopic g) :
    (reindex hm hn f).Homotopic (reindex hm hn g) := by
  subst m'
  subst n'
  exact h

end NoExoticSixSphere.SphereMapSuspension

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [Nonempty M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}

theorem sixthStableClass_eq_of_same_frame (d d' : e.FramedCollapseData a)
    (hd : 8 ≤ e.ambientDimension) : d.sixthStableClass hd = d'.sixthStableClass hd := by
  apply StableSixSphereMaps.ofMap_eq_of_homotopic
  exact SphereMapSuspension.reindex_homotopic (by omega) (by omega)
    (d.sphereMap_homotopic d')

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
