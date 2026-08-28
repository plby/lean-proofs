import Wikipedia.NoExoticSixSphere.SphereTangentRemainderMiddle
import Wikipedia.NoExoticSixSphere.SphereRemovedDiskSheetGerms

/-!
# Source-only tangent remainders on both retained caps

The actual folded reference frames use the removed-disk sheet germs. Their
target derivatives cancel in the retained product coordinates. The fixed
pole-Jacobian corrections remain as genuine three-dimensional factors, so
neither a reflection nor a coordinate twist is discarded.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace SphereSumNeck

open GLOrthonormalization SphereThreeTangentFrame SphereHemisphereRetraction

def northTangentRemainder (ε : ℝ) (hε : 0 < ε) (x : North) : Vector 3 →L[ℝ] Vector 6 :=
  (EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    (framedDerivative leftSourceCoordinate
      (northCapHomeomorph ε hε (northRetainedCap (reflectHead x.val))))).comp
        (northTangentInverseJacobian ε hε
          (ClosedHemisphere.center (spherePole 3))).symm.toContinuousLinearMap

def southTangentRemainder (ε : ℝ) (hε : 0 < ε) (x : North) : Vector 3 →L[ℝ] Vector 6 :=
  (EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
    (framedDerivative rightSourceCoordinate
      (southCapHomeomorph ε hε (southRetainedCap (reflectHead x.val))))).comp
        (southTangentInverseJacobian ε hε
          (ClosedHemisphere.center (spherePole 3))).symm.toContinuousLinearMap

end SphereSumNeck

namespace Stiefel.Monomorphism

open GLOrthonormalization

theorem fixedSourceRecoordinate_apply {N n : ℕ} (V : Vector n ≃L[ℝ] Vector n)
    (F : C(Sphere 3, Space N n)) (x : Sphere 3) :
    (fixedSourceRecoordinate V F x).val = (F x).val.comp V.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

end Stiefel.Monomorphism

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel SphereSumNeck FrameBlockCoordinates SphereHemisphereRetraction

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem northCapReferenceFrameMap_apply (F : C(Sphere 3, M))
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
    (ε : ℝ) (hε : 0 < ε) (x : Sphere 3) :
    (e.northCapReferenceFrameMap ν F hF hFi ε hε x).val =
      (e.sphereFrameOperator ν F (northCapHomeomorph ε hε x)).comp
        (identityBlockOperator (e.ambientDimension - 6)
          (northTangentInverseJacobian ε hε
            (ClosedHemisphere.center (spherePole 3))).symm.toContinuousLinearMap) := by
  unfold northCapReferenceFrameMap
  rw [Monomorphism.fixedSourceRecoordinate_apply,
    northCapInverseJacobian_eq_identityBlock, identityBlockEquiv_symm,
    identityBlockEquiv_toContinuousLinearMap]
  rfl

theorem southCapReferenceFrameMap_apply (G : C(Sphere 3, M))
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))
    (ε : ℝ) (hε : 0 < ε) (x : Sphere 3) :
    (e.southCapReferenceFrameMap ν G hG hGi ε hε x).val =
      (e.sphereFrameOperator ν G (southCapHomeomorph ε hε x)).comp
        (identityBlockOperator (e.ambientDimension - 6)
          (southTangentInverseJacobian ε hε
            (ClosedHemisphere.center (spherePole 3))).symm.toContinuousLinearMap) := by
  unfold southCapReferenceFrameMap
  rw [Monomorphism.fixedSourceRecoordinate_apply,
    southCapInverseJacobian_eq_identityBlock, identityBlockEquiv_symm,
    identityBlockEquiv_toContinuousLinearMap]
  rfl

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

theorem tangentResolutionFrameRemainder_north (x : North) :
    (e.tangentResolutionFrameRemainder ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi (northRetainedCap x.val)).val =
        northTangentRemainder ε hε x := by
  let y := northCapHomeomorph ε hε (northRetainedCap (reflectHead x.val))
  have hy : y ∈ removedSourceDisk ε := foldedNorthSource_mem_removed ε hε x
  have hs := leftSourceCoordinate_mem_source Φ hε hprod hy
  let K := gluedSphereMap Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG
  let hK := contMDiff_gluedSphere Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG
  let hKi := injective_mfderiv_gluedSphere Φ F G hε hprod ha hleft hright hF hG hFi hGi
  have hcN := e.twoCapNormalizedFrameMap_north ν K hK hKi ε hε F hF hFi
    (gluedSphere_eventuallyEq_northHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft)
  have hcS := e.twoCapNormalizedFrameMap_south ν K hK hKi ε hε G hG hGi
    (gluedSphere_eventuallyEq_southHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hright)
  have hRm : e.resolutionFrameRemainder ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi (northRetainedCap x.val) =
      e.northCapReferenceFrameMap ν F hF hFi ε hε (northRetainedCap (reflectHead x.val)) :=
    HemisphereExchange.twoCapRemainder_north _ _ _ hcN hcS x
  have hR : (e.resolutionFrameRemainder ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi (northRetainedCap x.val)).val =
      (e.sphereFrameOperator ν F y).comp (identityBlockOperator (e.ambientDimension - 6)
        (northTangentInverseJacobian ε hε
          (ClosedHemisphere.center (spherePole 3))).symm.toContinuousLinearMap) := by
    rw [hRm]
    exact e.northCapReferenceFrameMap_apply ν F hF hFi ε hε _
  have hq : productParameterInclusion Φ hprod
      (remainderChartParameter Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG
        (northRetainedCap x.val)) = ⟨leftSourceCoordinate y, hs⟩ :=
    Subtype.ext (remainderChartParameter_north Φ F G hε ⟨ha.1.le, ha.2⟩
      hprod hleft hright hF hG x)
  rw [e.tangentResolutionFrameRemainder_operator, hq, hR,
    ← ContinuousLinearMap.comp_assoc]
  rw [e.sphereFrameOperator_product_reduced ν Φ F leftSourceCoordinate y hs
    ((contMDiffAt_leftSourceCoordinate hy).mdifferentiableAt (by simp))
    (leftSheet_eventuallyEq Φ hε hprod F hleft hy), lowerTangentBlock_identityBlock]
  rfl

theorem tangentResolutionFrameRemainder_south (x : North) :
    (e.tangentResolutionFrameRemainder ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi (southRetainedCap x.val)).val =
        southTangentRemainder ε hε x := by
  let y := southCapHomeomorph ε hε (southRetainedCap (reflectHead x.val))
  have hy : y ∈ removedSourceDisk ε := foldedSouthSource_mem_removed ε hε x
  have hs := rightSourceCoordinate_mem_source Φ hε hprod hy
  let K := gluedSphereMap Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG
  let hK := contMDiff_gluedSphere Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG
  let hKi := injective_mfderiv_gluedSphere Φ F G hε hprod ha hleft hright hF hG hFi hGi
  have hcN := e.twoCapNormalizedFrameMap_north ν K hK hKi ε hε F hF hFi
    (gluedSphere_eventuallyEq_northHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft)
  have hcS := e.twoCapNormalizedFrameMap_south ν K hK hKi ε hε G hG hGi
    (gluedSphere_eventuallyEq_southHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hright)
  have hRm : e.resolutionFrameRemainder ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi (southRetainedCap x.val) =
      e.southCapReferenceFrameMap ν G hG hGi ε hε (southRetainedCap (reflectHead x.val)) :=
    HemisphereExchange.twoCapRemainder_south _ _ _ hcN hcS x
  have hR : (e.resolutionFrameRemainder ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi (southRetainedCap x.val)).val =
      (e.sphereFrameOperator ν G y).comp (identityBlockOperator (e.ambientDimension - 6)
        (southTangentInverseJacobian ε hε
          (ClosedHemisphere.center (spherePole 3))).symm.toContinuousLinearMap) := by
    rw [hRm]
    exact e.southCapReferenceFrameMap_apply ν G hG hGi ε hε _
  have hq : productParameterInclusion Φ hprod
      (remainderChartParameter Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG
        (southRetainedCap x.val)) = ⟨rightSourceCoordinate y, hs⟩ :=
    Subtype.ext (remainderChartParameter_south Φ F G hε ⟨ha.1.le, ha.2⟩
      hprod hleft hright hF hG x)
  rw [e.tangentResolutionFrameRemainder_operator, hq, hR,
    ← ContinuousLinearMap.comp_assoc]
  rw [e.sphereFrameOperator_product_reduced ν Φ G rightSourceCoordinate y hs
    ((contMDiffAt_rightSourceCoordinate hy).mdifferentiableAt (by simp))
    (rightSheet_eventuallyEq Φ hε hprod G hright hy), lowerTangentBlock_identityBlock]
  rfl

end EuclideanEmbedding

end NoExoticSixSphere
