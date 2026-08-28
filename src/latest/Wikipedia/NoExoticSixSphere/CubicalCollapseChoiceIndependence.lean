import Wikipedia.NoExoticSixSphere.CubicalStableSixVanishing
import Wikipedia.NoExoticSixSphere.StableCollapseChoiceIndependence

/-!
# Collapse choices give the same element of the actual native stable group

The equality uses actual homotopies of the sphere representatives and the
proved comparison with native based homotopy groups. It is stronger than
an equivalence of vanishing predicates. The embedding and normal frame
are fixed throughout; no comparison of different framings is inferred.
-/

noncomputable section

namespace NoExoticSixSphere.CubicalStableSix

open StableSixSphereMaps SmoothCube

theorem sphereClass_eq_of_homotopic {k : ℕ} (f g : BasedStage k)
    (h : f.val.Homotopic g.val) : sphereClass f = sphereClass g := by
  apply (nativeStageEquiv k).injective
  rw [nativeStageEquiv_sphereClass, nativeStageEquiv_sphereClass]
  exact (classOf_eq_iff _ _).mpr h

theorem ofNative_sphereClass_eq_of_homotopic {k : ℕ} (f g : BasedStage k)
    (h : f.val.Homotopic g.val) : ofNative (sphereClass f) = ofNative (sphereClass g) :=
  congrArg ofNative (sphereClass_eq_of_homotopic f g h)

end NoExoticSixSphere.CubicalStableSix

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [Nonempty M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}

theorem nativeSixthStageClass_eq_of_same_frame (d d' : e.FramedCollapseData a)
    (hd : 8 ≤ e.ambientDimension) :
    d.nativeSixthStageClass hd = d'.nativeSixthStageClass hd := by
  apply CubicalStableSix.sphereClass_eq_of_homotopic
  exact SphereMapSuspension.reindex_homotopic (by omega) (by omega)
    (d.sphereMap_homotopic d')

theorem cubicalStableClass_eq_of_same_frame (d d' : e.FramedCollapseData a)
    (hd : 8 ≤ e.ambientDimension) : d.cubicalStableClass hd = d'.cubicalStableClass hd :=
  congrArg CubicalStableSix.ofNative (d.nativeSixthStageClass_eq_of_same_frame d' hd)

end NoExoticSixSphere.EuclideanEmbedding.FramedCollapseData
