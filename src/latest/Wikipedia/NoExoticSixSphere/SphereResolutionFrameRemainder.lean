import Wikipedia.NoExoticSixSphere.SphereGluedFrameRemainder
import Wikipedia.NoExoticSixSphere.SphereSumGluingImmersion

/-!
# The frame remainder of the actually constructed immersed resolution

All cap-germ hypotheses of the remainder construction are discharged for
the original glued sphere. Its smoothness and injective native derivatives
are supplied by the existing resolution theorems. The remainder is a
specified continuous operator map; its numerical parity is not assigned.
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

def resolutionFrameRemainder :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)) :=
  e.gluedFrameRemainder ν
    (gluedSphereMap Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG) F G
    (contMDiff_gluedSphere Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG) hF hG
    (injective_mfderiv_gluedSphere Φ F G hε hprod ha hleft hright hF hG hFi hGi) hFi hGi ε hε
    (gluedSphere_eventuallyEq_northHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft)
    (gluedSphere_eventuallyEq_southHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hright)

theorem resolutionFrameParity_decomposition :
    e.sphereDerivativeParity ν (gluedSphere Φ ε a F G)
        (contMDiff_gluedSphere Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG)
        (injective_mfderiv_gluedSphere Φ F G hε hprod ha hleft hright hF hG hFi hGi) =
      e.sphereDerivativeParity ν F hF hFi + e.sphereDerivativeParity ν G hG hGi +
        Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
          (by have h := e.dimension_le_ambient (F (Stiefel.pole 3)); omega) (by omega)
          (e.resolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi) :=
  e.sphereDerivativeParity_eq_inputs_add_remainder ν
    (gluedSphereMap Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG) F G
    (contMDiff_gluedSphere Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG) hF hG
    (injective_mfderiv_gluedSphere Φ F G hε hprod ha hleft hright hF hG hFi hGi) hFi hGi ε hε
    (gluedSphere_eventuallyEq_northHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft)
    (gluedSphere_eventuallyEq_southHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hright)

end NoExoticSixSphere.EuclideanEmbedding
