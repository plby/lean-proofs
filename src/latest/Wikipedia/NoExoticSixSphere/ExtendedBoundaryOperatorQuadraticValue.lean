import Wikipedia.NoExoticSixSphere.ExtendedBoundaryOperatorReflection

/-!
# The original quadratic value from an exact boundary-operator extension

Either uniform collar sign is allowed. The smooth disk may have interior
singularities: the hypothesis is an extension through injective operators
of its actual stabilized boundary operator with the prescribed raw frame.
This proves the original quadratic value, not a newly assigned invariant.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel CollaredDiskFrame
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

theorem quadraticValue_zero_of_extended_boundary_operator
    (f : C(Sphere 3, M)) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ F x)
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (G : C(Disk (E := Vector 4),
      Monomorphism.Space (e.ambientDimension + 6) (((e.ambientDimension - 6) + 5) + 4)))
    (hG : ∀ s, (G (boundaryToDisk s)).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp
        (a.ambient (f s))) (fderiv ℝ F s.val))
    (hheight : (∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) ∨
      (∀ s : Sphere 3, (fderiv ℝ F s.val s.val).2 < 0)) :
    e.modTwoHomologyQuadraticForm a r m (SixSphereMiddleParity.sphereClass f) = 0 := by
  rw [e.modTwoHomologyQuadraticForm_sphereClass,
    e.geometricSphereParity_eq_of_embedding a r f hf hi hd]
  rcases hheight with hp | hn
  · exact e.sphereParity_zero_of_extended_boundary_operator a f hf hi hd F hF hb G hG hp
  · exact e.sphereParity_zero_of_extended_boundary_operator_negative a f hf hi hd F hF hb G hG hn

end NoExoticSixSphere.EuclideanEmbedding
