import Wikipedia.NoExoticSixSphere.ContractedProductFrameCoordinates
import Wikipedia.NoExoticSixSphere.SphereRemainderNormalColumns
import Wikipedia.NoExoticSixSphere.SphereRemainderChartFormula

/-!
# Parity-preserving target normalization of the actual resolution remainder

The target coordinate field is evaluated at the proved chart parameter and
contracts within the retained closed product. It therefore preserves the
actual remainder parity. Its normal columns are exactly the standard identity
columns, by the checked relation to the constructed basepoint map. The
remaining tangent-operator comparison and numerical parity are not asserted.
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

def normalizedResolutionFrameRemainder :
    C(Sphere 3, Monomorphism.Space ((e.ambientDimension - 6) + 6)
      ((e.ambientDimension - 6) + 3)) :=
  e.targetProductRecoordinate ν Φ hprod
    (remainderChartParameter Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG)
    (e.resolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi)

theorem normalizedResolutionFrameRemainder_parity :
    Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1) (by omega) (by omega)
      (e.normalizedResolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi) =
    Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
      (by have h := e.dimension_le_ambient (F (Stiefel.pole 3)); omega) (by omega)
      (e.resolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi) :=
  e.targetProductRecoordinate_parity ν Φ hprod hε ((e.ambientDimension - 6) + 1)
    (by have h := e.dimension_le_ambient (F (Stiefel.pole 3)); omega) (by omega) _ _

theorem normalizedResolutionFrameRemainder_normal (x : Sphere 3)
    (v : Vector (e.ambientDimension - 6)) :
    (e.normalizedResolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi x).val
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 6)) := by
  let q := remainderChartParameter Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG
  let R := e.resolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi
  have hR (y : Sphere 3) (w : Vector (e.ambientDimension - 6)) :
      (R y).val (EuclideanSpace.finAddEquivProd.symm (w, (0 : Vector 3))) =
        (ν.orthonormal (Φ (q y).val)).val w := by
    calc
      _ = (ν.orthonormal
          (remainderBasepoint Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG y)).val w :=
        e.resolutionFrameRemainder_normal ν Φ F G hε ha hprod hleft hright hF hG hFi hGi y w
      _ = _ := (congrArg (fun p : M ↦ (ν.orthonormal p).val w)
        (chart_remainderChartParameter Φ F G hε ⟨ha.1.le, ha.2⟩
          hprod hleft hright hF hG y)).symm
  exact e.targetProductRecoordinate_normal ν Φ hprod q R hR x v

theorem resolutionFrameParity_normalized_decomposition :
    e.sphereDerivativeParity ν (gluedSphere Φ ε a F G)
        (contMDiff_gluedSphere Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG)
        (injective_mfderiv_gluedSphere Φ F G hε hprod ha hleft hright hF hG hFi hGi) =
      e.sphereDerivativeParity ν F hF hFi + e.sphereDerivativeParity ν G hG hGi +
        Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
          (by omega) (by omega)
          (e.normalizedResolutionFrameRemainder ν Φ F G hε ha hprod
            hleft hright hF hG hFi hGi) := by
  rw [e.normalizedResolutionFrameRemainder_parity]
  exact e.resolutionFrameParity_decomposition ν Φ F G hε ha hprod hleft hright hF hG hFi hGi

end NoExoticSixSphere.EuclideanEmbedding
