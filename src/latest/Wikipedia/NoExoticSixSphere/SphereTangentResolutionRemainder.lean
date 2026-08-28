import Wikipedia.NoExoticSixSphere.FixedNormalOperatorReduction
import Wikipedia.NoExoticSixSphere.SphereNormalizedResolutionRemainder

/-!
# The actual resolution remainder reduced to its three-to-six tangent operator

The proved identity normal columns allow an injective upper-triangular
homotopy, not an assumed block-diagonal equality. Removing the resulting
identity block preserves parity. This gives an actual unstabilized remainder
in the original resolution formula; its comparison with the Whitney
reference is still a separate mathematical obligation.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : C(Sphere 3, M)) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Ioc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
  (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
  (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
  (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))

def tangentResolutionFrameRemainder : C(Sphere 3, Monomorphism.Space 6 3) :=
  Monomorphism.fixedNormalReduction (e.ambientDimension - 6)
    (e.normalizedResolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi)
    (e.normalizedResolutionFrameRemainder_normal ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi)

theorem tangentResolutionFrameRemainder_apply (x : Sphere 3) (w : Vector 3) :
    (e.tangentResolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi x).val w =
      (EuclideanSpace.finAddEquivProd
        ((e.normalizedResolutionFrameRemainder ν Φ F G hε ha hprod
          hleft hright hF hG hFi hGi x).val
            (EuclideanSpace.finAddEquivProd.symm ((0 : Vector (e.ambientDimension - 6)), w)))).2 :=
  rfl

def tangentResolutionFrameRemainderHomotopy :
    (e.normalizedResolutionFrameRemainder ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi).Homotopy
        ((Monomorphism.frontBlockMap (e.ambientDimension - 6)).comp
          (e.tangentResolutionFrameRemainder ν Φ F G hε ha hprod
            hleft hright hF hG hFi hGi)) :=
  Monomorphism.fixedNormalReductionHomotopy (e.ambientDimension - 6)
    (e.normalizedResolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi)
    (e.normalizedResolutionFrameRemainder_normal ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi)

theorem tangentResolutionFrameRemainder_normalized_parity :
    Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1) (by omega) (by omega)
        (e.normalizedResolutionFrameRemainder ν Φ F G hε ha hprod
          hleft hright hF hG hFi hGi) =
      Monomorphism.sphereParityOfDimension 1 rfl rfl
        (e.tangentResolutionFrameRemainder ν Φ F G hε ha hprod
          hleft hright hF hG hFi hGi) :=
  Monomorphism.sphereParityOfDimension_fixedNormalReduction (e.ambientDimension - 6)
    1 rfl rfl _ _

theorem tangentResolutionFrameRemainder_parity :
    Monomorphism.sphereParityOfDimension 1 rfl rfl
        (e.tangentResolutionFrameRemainder ν Φ F G hε ha hprod
          hleft hright hF hG hFi hGi) =
      Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
        (by have h := e.dimension_le_ambient (F (Stiefel.pole 3)); omega) (by omega)
        (e.resolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi) := by
  rw [← e.tangentResolutionFrameRemainder_normalized_parity]
  exact e.normalizedResolutionFrameRemainder_parity ν Φ F G hε ha hprod
    hleft hright hF hG hFi hGi

theorem resolutionFrameParity_tangent_decomposition :
    e.sphereDerivativeParity ν (gluedSphere Φ ε a F G)
        (contMDiff_gluedSphere Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG)
        (injective_mfderiv_gluedSphere Φ F G hε hprod ha hleft hright hF hG hFi hGi) =
      e.sphereDerivativeParity ν F hF hFi + e.sphereDerivativeParity ν G hG hGi +
        Monomorphism.sphereParityOfDimension 1 rfl rfl
          (e.tangentResolutionFrameRemainder ν Φ F G hε ha hprod
            hleft hright hF hG hFi hGi) := by
  rw [e.resolutionFrameParity_normalized_decomposition,
    e.tangentResolutionFrameRemainder_normalized_parity]

end NoExoticSixSphere.EuclideanEmbedding
