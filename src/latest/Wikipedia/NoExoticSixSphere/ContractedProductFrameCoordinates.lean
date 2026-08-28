import Wikipedia.NoExoticSixSphere.ProductNormalChartCoordinates
import Wikipedia.NoExoticSixSphere.SphereRemainderChartParameter

/-!
# Target-coordinate normalization through the contracted product parameter

The actual inverse normal-product coordinates vary continuously on the
closed retained chart product. Its explicit contraction makes their action
on a sphere of injective operators parity-preserving. No arbitrary
sphere-dependent target coordinate change is treated as extendible.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞) {ε : ℝ}
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)

def productParameterInclusion : C(RemainderParameters ε, Φ.source) :=
  ⟨fun p ↦ ⟨p.val, hprod p.property⟩, continuous_subtype_val.subtype_mk _⟩

end SphereSumNeck

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞) {ε : ℝ}
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)

def productParameterInverse (p : RemainderParameters ε) :
    Vector e.ambientDimension ≃L[ℝ] Vector ((e.ambientDimension - 6) + 6) :=
  (e.normalProductCoordinates ν Φ (productParameterInclusion Φ hprod p)).symm

theorem continuous_productParameterInverse :
    Continuous (fun p ↦ (e.productParameterInverse ν Φ hprod p).toContinuousLinearMap) :=
  (e.continuous_inverse_normalProductCoordinates ν Φ).comp
    (productParameterInclusion Φ hprod).continuous

def targetProductRecoordinate {n : ℕ} (q : C(Sphere 3, RemainderParameters ε))
    (R : C(Sphere 3, Monomorphism.Space e.ambientDimension n)) :
    C(Sphere 3, Monomorphism.Space ((e.ambientDimension - 6) + 6) n) :=
  Monomorphism.parameterRecoordinate (e.productParameterInverse ν Φ hprod)
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector n))
    (e.continuous_productParameterInverse ν Φ hprod) continuous_const q R

theorem targetProductRecoordinate_apply {n : ℕ} (q : C(Sphere 3, RemainderParameters ε))
    (R : C(Sphere 3, Monomorphism.Space e.ambientDimension n)) (x : Sphere 3) (v : Vector n) :
    (e.targetProductRecoordinate ν Φ hprod q R x).val v =
      (e.normalProductCoordinates ν Φ (productParameterInclusion Φ hprod (q x))).symm
        ((R x).val v) := rfl

theorem targetProductRecoordinate_parity {n : ℕ} (hε : 0 < ε)
    (r : ℕ) (hN : e.ambientDimension = 3 + (r + 2)) (hn : n = r + 2)
    (q : C(Sphere 3, RemainderParameters ε))
    (R : C(Sphere 3, Monomorphism.Space e.ambientDimension n)) :
    Monomorphism.sphereParityOfDimension r
      (by have h := e.dimension_le_ambient (Φ 0); omega) hn
      (e.targetProductRecoordinate ν Φ hprod q R) =
      Monomorphism.sphereParityOfDimension r hN hn R :=
  Monomorphism.sphereParityOfDimension_parameterRecoordinate
    (e.productParameterInverse ν Φ hprod) (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector n))
    (e.continuous_productParameterInverse ν Φ hprod) continuous_const
    r r hN hn (by have h := e.dimension_le_ambient (Φ 0); omega) hn q R
    (remainderParameterZero ε hε) (remainderParameterContraction ε hε q)

theorem targetProductRecoordinate_normal (q : C(Sphere 3, RemainderParameters ε))
    (R : C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)))
    (hR : ∀ x v, (R x).val (EuclideanSpace.finAddEquivProd.symm
      (v, (0 : Vector 3))) = (ν.orthonormal (Φ (q x).val)).val v)
    (x : Sphere 3) (v : Vector (e.ambientDimension - 6)) :
    (e.targetProductRecoordinate ν Φ hprod q R x).val
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 6)) := by
  rw [e.targetProductRecoordinate_apply, hR x v]
  exact e.inverse_normalProductCoordinates_normal ν Φ (productParameterInclusion Φ hprod (q x)) v

end EuclideanEmbedding
end NoExoticSixSphere
