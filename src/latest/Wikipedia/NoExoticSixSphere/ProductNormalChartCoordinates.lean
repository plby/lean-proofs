import Wikipedia.NoExoticSixSphere.ManifoldNormalChartCoordinates

/-!
# Genuine normal and tangent coordinates for a retained product chart

Convert the original product chart to the six-dimensional Euclidean model
using the fixed product equivalence. The existing normal-chart construction
then gives continuous invertible ambient coordinates on the entire original
chart source, with a continuous inverse and the exact normal-column values.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace ProductChartCoordinates

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

def productTargetChart : PartialDiffeomorph (𝓡 6) (𝓡 6) M (Vector 6) ∞ :=
  Φ.symm.trans
    (EuclideanSpace.finAddEquivProd (n := 3) (m := 3)).symm.toDiffeomorph.toPartialDiffeomorph

theorem productTargetChart_source : (productTargetChart Φ).source = Φ.target := by
  ext x
  change (x ∈ Φ.target ∧ Φ.symm x ∈ (univ : Set (Vector 3 × Vector 3))) ↔ x ∈ Φ.target
  simp only [mem_univ, and_true]

theorem productTargetChart_apply (x : M) :
    productTargetChart Φ x = EuclideanSpace.finAddEquivProd.symm (Φ.symm x) := rfl

theorem productTargetChart_symm_apply (x : Vector 6) :
    (productTargetChart Φ).symm x = Φ (EuclideanSpace.finAddEquivProd x) := rfl

def productChartPoint : C(Φ.source, (productTargetChart Φ).source) where
  toFun z := ⟨Φ z.val, Φ.map_source z.property, mem_univ _⟩
  continuous_toFun := Φ.toOpenPartialHomeomorph.continuousOn.domRestrict.subtype_mk _

theorem productTargetChart_point (z : Φ.source) :
    productTargetChart Φ (productChartPoint Φ z).val =
      EuclideanSpace.finAddEquivProd.symm z.val :=
  congrArg EuclideanSpace.finAddEquivProd.symm (Φ.left_inv z.property)

end ProductChartCoordinates

namespace EuclideanEmbedding

open GLOrthonormalization ProductChartCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

def normalProductCoordinates (z : Φ.source) :
    Vector ((e.ambientDimension - 6) + 6) ≃L[ℝ] Vector e.ambientDimension :=
  e.normalChartCoordinates ν (productTargetChart Φ) (productChartPoint Φ z)

theorem continuous_normalProductCoordinates :
    Continuous (fun z ↦ (e.normalProductCoordinates ν Φ z).toContinuousLinearMap) :=
  (e.continuous_normalChartCoordinates ν (productTargetChart Φ)).comp
    (productChartPoint Φ).continuous

theorem continuous_inverse_normalProductCoordinates :
    Continuous (fun z ↦ (e.normalProductCoordinates ν Φ z).symm.toContinuousLinearMap) :=
  (e.continuous_inverse_normalChartCoordinates ν (productTargetChart Φ)).comp
    (productChartPoint Φ).continuous

theorem normalProductCoordinates_normal (z : Φ.source) (v : Vector (e.ambientDimension - 6)) :
    e.normalProductCoordinates ν Φ z (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 6))) =
      (ν.orthonormal (Φ z.val)).val v := by
  change e.normalChartOperator ν (productTargetChart Φ) (productChartPoint Φ z)
    (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 6))) = _
  rw [e.normalChartOperator_apply, ContinuousLinearEquiv.apply_symm_apply, map_zero, add_zero]
  rfl

theorem inverse_normalProductCoordinates_normal (z : Φ.source)
    (v : Vector (e.ambientDimension - 6)) :
    (e.normalProductCoordinates ν Φ z).symm ((ν.orthonormal (Φ z.val)).val v) =
      EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 6)) := by
  apply (e.normalProductCoordinates ν Φ z).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, e.normalProductCoordinates_normal]

theorem chartEmbeddingDerivative_product (z : Φ.source) :
    e.chartEmbeddingDerivative (productTargetChart Φ) (productChartPoint Φ z) =
      (fderiv ℝ (e.toFun ∘ Φ) z.val).comp
        (EuclideanSpace.finAddEquivProd (n := 3) (m := 3)).toContinuousLinearMap := by
  let L : Vector 6 ≃L[ℝ] (Vector 3 × Vector 3) :=
    EuclideanSpace.finAddEquivProd (n := 3) (m := 3)
  have hΦ := Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds z.property)
  have he : ContDiffAt ℝ ∞ (e.toFun ∘ Φ) z.val :=
    (e.smooth.contMDiffAt.comp z.val hΦ).contDiffAt
  have hd : DifferentiableAt ℝ (e.toFun ∘ Φ) (L (L.symm z.val)) := by
    rw [L.apply_symm_apply]
    exact he.differentiableAt (by simp)
  have h := fderiv_comp (L.symm z.val) hd L.differentiableAt
  rw [L.apply_symm_apply, L.fderiv] at h
  change fderiv ℝ (e.toFun ∘ (productTargetChart Φ).symm)
    (productTargetChart Φ (productChartPoint Φ z).val) = _
  rw [productTargetChart_point]
  exact h

theorem normalProductCoordinates_tangent (z : Φ.source) (w : Vector 3 × Vector 3) :
    e.normalProductCoordinates ν Φ z (EuclideanSpace.finAddEquivProd.symm
      ((0 : Vector (e.ambientDimension - 6)), EuclideanSpace.finAddEquivProd.symm w)) =
      fderiv ℝ (e.toFun ∘ Φ) z.val w := by
  change e.normalChartOperator ν (productTargetChart Φ) (productChartPoint Φ z) _ = _
  rw [e.normalChartOperator_apply, ContinuousLinearEquiv.apply_symm_apply, map_zero, zero_add,
    e.chartEmbeddingDerivative_product, ContinuousLinearMap.comp_apply]
  exact congrArg (fderiv ℝ (e.toFun ∘ Φ) z.val)
    ((EuclideanSpace.finAddEquivProd (n := 3) (m := 3)).apply_symm_apply w)

end EuclideanEmbedding
end NoExoticSixSphere
