import Wikipedia.NoExoticSixSphere.SphereLinearFrameCoordinates
import Wikipedia.NoExoticSixSphere.SphereDoublePointReparametrization
import Wikipedia.NoExoticSixSphere.ImmersedSphereCorrectedParity

/-!
# Immersed corrected parity is invariant under a linear sphere isometry

The exact collar chain rule gives a constant source-coordinate change in
the original twisted operator. It preserves disk extension, as does the
linear reparametrization of the boundary sphere itself. The actual unordered
double-point orbit bijection handles the other term. Orientation preservation
and extension of the quaternionic tangent frame are not assumed.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel SpanningDiskFrameCoordinates SphereLinearReparametrization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (L : Vector 4 ≃ₗᵢ[ℝ] Vector 4) (f : Sphere 3 → M)
  (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))

theorem immersedSphereFrameParity_precomp_linear :
    e.immersedSphereFrameParity a (f ∘ sphereMap L)
      (hf.comp (sphereDiffeomorph L).contMDiff_toFun) (injective_mfderiv_precomp L f hf hd) =
      e.immersedSphereFrameParity a f hf hd := by
  apply zmodTwo_eq_of_zero_iff
  rw [immersedSphereFrameParity_zero_iff, immersedSphereFrameParity_zero_iff]
  let F := twistedBlockMap (e.sphereFrameOperatorMap a f hf hd)
  let G := twistedBlockMap (e.sphereFrameOperatorMap a (f ∘ sphereMap L)
    (hf.comp (sphereDiffeomorph L).contMDiff_toFun) (injective_mfderiv_precomp L f hf hd))
  have hc : DiskBoundary.Extends G ↔ DiskBoundary.Extends (F.comp (sphereMap L)) :=
    Monomorphism.extends_recoordinate_iff
      (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector (e.ambientDimension + 6)))
      (fun _ ↦ sourceBlock L (e.ambientDimension - 6))
      continuous_const continuous_const continuous_const continuous_const
      (F.comp (sphereMap L)) G (e.twistedSphereFrame_precomp_linear a L f hf hd)
  exact hc.trans (extends_precomp_iff L F)

theorem immersedSphereCorrectedParity_precomp_linear :
    e.immersedSphereCorrectedParity a (f ∘ sphereMap L)
      (hf.comp (sphereDiffeomorph L).contMDiff_toFun) (injective_mfderiv_precomp L f hf hd) =
      e.immersedSphereCorrectedParity a f hf hd := by
  unfold immersedSphereCorrectedParity
  exact congrArg₂ (· + ·) (e.immersedSphereFrameParity_precomp_linear a L f hf hd)
    (SphereSelfIntersections.unorderedParity_precomp_equiv f (sphereDiffeomorph L).toEquiv)

end NoExoticSixSphere.EuclideanEmbedding
