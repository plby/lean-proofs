import Wikipedia.NoExoticSixSphere.CollaredDiskHeightReflection

/-!
# The original quadratic form vanishes on a class with a framed collar disk

This applies the actual sphere-parity theorem to the proved geometric
quadratic refinement on native middle homology. Either uniform collar
sign is allowed. It remains to construct such witnesses for all classes
in the kernel of the actual boundary inclusion; that is not assumed here.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

theorem quadraticValue_zero_of_framed_collared_disk
    (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hDF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Injective (fderiv ℝ F x))
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (A : C(Disk (E := Vector 4), e.NormalModel →L[ℝ] (Vector e.ambientDimension × ℝ)))
    (hA : ∀ x, Injective (A x))
    (hAD : ∀ x, Disjoint (A x).range (fderiv ℝ F x.val).range)
    (hAb : ∀ s, A (boundaryToDisk s) =
      (ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp (a.ambient (f s)))
    (hheight : (∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) ∨
      (∀ s : Sphere 3, (fderiv ℝ F s.val s.val).2 < 0)) :
    e.modTwoHomologyQuadraticForm a r m (SixSphereMiddleParity.sphereClass f) = 0 := by
  rw [e.modTwoHomologyQuadraticForm_sphereClass,
    e.geometricSphereParity_eq_of_embedding a r f hf hi hd]
  rcases hheight with hp | hn
  · exact e.sphereParity_zero_of_framed_collared_disk a f hf hi hd F hF hDF hb A hA hAD hAb hp
  · exact e.sphereParity_zero_of_framed_collared_disk_negative a f hf hi hd
      F hF hDF hb A hA hAD hAb hn

end NoExoticSixSphere.EuclideanEmbedding
