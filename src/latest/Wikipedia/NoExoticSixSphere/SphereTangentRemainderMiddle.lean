import Wikipedia.NoExoticSixSphere.SphereTangentResolutionRemainder
import Wikipedia.NoExoticSixSphere.SphereProductFrameCancellation
import Wikipedia.NoExoticSixSphere.SphereCapTangentCoordinates

/-!
# The source-only tangent remainder on the middle region

Between the retained caps, the actual exchanged operator is the source-
normalized frame of the original glued sphere. Its genuine chart parameter
is the capped-neck map. Cancelling the product-chart derivative leaves an
explicit three-to-six operator independent of all target-manifold data.
-/

noncomputable section

open Set Function Metric Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace SphereSumNeck

open GLOrthonormalization SphereThreeTangentFrame

def middleRemainderCoordinate (ε a : ℝ) (x : Sphere 3) : Vector 3 × Vector 3 :=
  ε • capPair a (SphereCylinder.inverse 2 x)

theorem contMDiffAt_middleRemainderCoordinate (ε a : ℝ) {x : Sphere 3}
    (hx : x ∈ neckRegion) :
    ContMDiffAt (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) ∞ (middleRemainderCoordinate ε a) x := by
  have hc : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun _ : Sphere 3 ↦ ε) x := contMDiffAt_const
  exact hc.smul ((contMDiff_capPair_slice a).contMDiffAt.comp x
    (SphereCylinder.contMDiffAt_inverse 2 (neckRegion_mem_band hx)))

def middleTangentRemainder (ε a : ℝ) (hε : 0 < ε) (x : Sphere 3) :
    Vector 3 →L[ℝ] Vector 6 :=
  (EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    (framedDerivative (middleRemainderCoordinate ε a) x)).comp
      (twoCapTangentCoordinates ε hε x).toContinuousLinearMap

end SphereSumNeck

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel SphereSumNeck FrameBlockCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem twoCapNormalizedFrameMap_apply (K : C(Sphere 3, M))
    (hK : ContMDiff (𝓡 3) (𝓡 6) ∞ K)
    (hKi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x))
    (ε : ℝ) (hε : 0 < ε) (x : Sphere 3) :
    (e.twoCapNormalizedFrameMap ν K hK hKi ε hε x).val =
      (e.sphereFrameOperator ν K x).comp
        (identityBlockOperator (e.ambientDimension - 6)
          (twoCapTangentCoordinates ε hε x).toContinuousLinearMap) :=
  twoCapSourceRecoordinate_apply (e.ambientDimension - 6) ε hε _ x

variable (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : C(Sphere 3, M)) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Ioc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
  (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
  (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
  (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))

theorem tangentResolutionFrameRemainder_operator (x : Sphere 3) :
    (e.tangentResolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi x).val =
      lowerTangentBlock (e.ambientDimension - 6)
        ((e.normalProductCoordinates ν Φ (productParameterInclusion Φ hprod
          (remainderChartParameter Φ F G hε ⟨ha.1.le, ha.2⟩ hprod
            hleft hright hF hG x))).symm.toContinuousLinearMap.comp
              (e.resolutionFrameRemainder ν Φ F G hε ha hprod
                hleft hright hF hG hFi hGi x).val) := rfl

theorem tangentResolutionFrameRemainder_middle (x : Sphere 3)
    (hN : (northRetainedCap.symm x).val 0 ≤ 0)
    (hS : (southRetainedCap.symm x).val 0 ≤ 0) :
    (e.tangentResolutionFrameRemainder ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi x).val = middleTangentRemainder ε a hε x := by
  let K := gluedSphereMap Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG
  let hK := contMDiff_gluedSphere Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG
  let hKi := injective_mfderiv_gluedSphere Φ F G hε hprod ha hleft hright hF hG hFi hGi
  have hcN := e.twoCapNormalizedFrameMap_north ν K hK hKi ε hε F hF hFi
    (gluedSphere_eventuallyEq_northHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft)
  have hcS := e.twoCapNormalizedFrameMap_south ν K hK hKi ε hε G hG hGi
    (gluedSphere_eventuallyEq_southHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hright)
  have hRm : e.resolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi x =
      e.twoCapNormalizedFrameMap ν K hK hKi ε hε x :=
    HemisphereExchange.twoCapRemainder_middle _ _ _ hcN hcS x hN hS
  have hR : (e.resolutionFrameRemainder ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi x).val =
      (e.sphereFrameOperator ν K x).comp (identityBlockOperator (e.ambientDimension - 6)
        (twoCapTangentCoordinates ε hε x).toContinuousLinearMap) := by
    rw [hRm]
    exact e.twoCapNormalizedFrameMap_apply ν K hK hKi ε hε x
  have hx := between_retained_caps_mem_neckRegion x hN hS
  have ht := neckRegion_time hx
  have hs : middleRemainderCoordinate ε a x ∈ Φ.source :=
    hprod (scaled_capPair_mem_product hε (by norm_num : (1 : ℝ) ≤ 4)
      a (SphereCylinder.inverse 2 x) ⟨ht.1.le, ht.2.le⟩)
  have hq : productParameterInclusion Φ hprod
      (remainderChartParameter Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG x) =
        ⟨middleRemainderCoordinate ε a x, hs⟩ :=
    Subtype.ext (remainderChartParameter_middle Φ F G hε ⟨ha.1.le, ha.2⟩
      hprod hleft hright hF hG x hN hS)
  have hgerm : (K : Sphere 3 → M) =ᶠ[𝓝 x] Φ ∘ middleRemainderCoordinate ε a := by
    filter_upwards [isOpen_neckRegion.mem_nhds hx] with y hy
    exact gluedSphere_middle Φ F G hy
  rw [e.tangentResolutionFrameRemainder_operator, hq, hR,
    ← ContinuousLinearMap.comp_assoc]
  rw [e.sphereFrameOperator_product_reduced ν Φ K (middleRemainderCoordinate ε a) x hs
    ((contMDiffAt_middleRemainderCoordinate ε a hx).mdifferentiableAt (by simp)) hgerm,
      lowerTangentBlock_identityBlock]
  rfl

end EuclideanEmbedding

end NoExoticSixSphere
