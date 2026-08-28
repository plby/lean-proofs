import Wikipedia.NoExoticSixSphere.ProductNormalChartCoordinates
import Wikipedia.NoExoticSixSphere.SphereLocalFrameChainRule
import Wikipedia.NoExoticSixSphere.FixedNormalOperatorReduction

/-!
# Exact cancellation of the retained product-chart derivative

For an original sphere map locally equal to the product chart of a specified
Euclidean map, the actual normal-product coordinates cancel the chart and
embedding derivatives. The remaining tangent operator is the quaternionically
framed derivative of that specified Euclidean map. This is a local identity,
not an assertion that arbitrary chart-contained frames are nullhomotopic.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace SphereThreeTangentFrame

open GLOrthonormalization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem framedDerivative_outer_comp_at (f : E → F) (g : Sphere 3 → E)
    (x : Sphere 3) (hf : DifferentiableAt ℝ f (g x))
    (hg : MDifferentiableAt (𝓡 3) 𝓘(ℝ, E) g x) :
    framedDerivative (f ∘ g) x = (fderiv ℝ f (g x)).comp (framedDerivative g x) := by
  have hm : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f (g x) := hf.mdifferentiableAt
  rw [framedDerivative_eq_native _ x (hm.comp x hg),
    framedDerivative_eq_native g x hg, mfderiv_comp x hm hg, mfderiv_eq_fderiv]
  rfl

end SphereThreeTangentFrame

namespace FrameBlockCoordinates

open GLOrthonormalization

theorem lowerTangentBlock_identityBlock (k : ℕ) {n N : ℕ}
    (C : Vector n →L[ℝ] Vector N) :
    lowerTangentBlock k (identityBlockOperator k C) = C := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [lowerTangentBlock_apply, identityBlockOperator_apply,
    ContinuousLinearEquiv.apply_symm_apply]

theorem lowerTangentBlock_identityBlock_comp (k : ℕ) {n m N : ℕ}
    (C : Vector n →L[ℝ] Vector N) (V : Vector (k + m) →L[ℝ] Vector (k + n)) :
    lowerTangentBlock k ((identityBlockOperator k C).comp V) =
      C.comp (lowerTangentBlock k V) := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [lowerTangentBlock_apply, ContinuousLinearMap.comp_apply,
    identityBlockOperator_apply, ContinuousLinearEquiv.apply_symm_apply]

end FrameBlockCoordinates

namespace EuclideanEmbedding

open GLOrthonormalization ProductChartCoordinates SphereThreeTangentFrame FrameBlockCoordinates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

theorem normalProductCoordinates_apply (z : Φ.source) (v : Vector (e.ambientDimension - 6))
    (w : Vector 3 × Vector 3) :
    e.normalProductCoordinates ν Φ z
        (EuclideanSpace.finAddEquivProd.symm (v, EuclideanSpace.finAddEquivProd.symm w)) =
      (ν.orthonormal (Φ z.val)).val v + fderiv ℝ (e.toFun ∘ Φ) z.val w := by
  change e.normalChartOperator ν (productTargetChart Φ) (productChartPoint Φ z) _ = _
  rw [e.normalChartOperator_apply, ContinuousLinearEquiv.apply_symm_apply,
    e.chartEmbeddingDerivative_product, ContinuousLinearMap.comp_apply]
  exact congrArg (fun u ↦ (ν.orthonormal (Φ z.val)).val v +
    fderiv ℝ (e.toFun ∘ Φ) z.val u)
      ((EuclideanSpace.finAddEquivProd (n := 3) (m := 3)).apply_symm_apply w)

theorem sphereFrameOperator_product_factorization (β : Sphere 3 → Vector 3 × Vector 3)
    (x : Sphere 3) (hx : β x ∈ Φ.source)
    (hβ : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) β x) :
    e.sphereFrameOperator ν (Φ ∘ β) x =
      (e.normalProductCoordinates ν Φ ⟨β x, hx⟩).toContinuousLinearMap.comp
        (identityBlockOperator (e.ambientDimension - 6)
          (EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
            (framedDerivative β x))) := by
  have hΦ := Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx)
  have he : DifferentiableAt ℝ (e.toFun ∘ Φ) (β x) :=
    (e.smooth.contMDiffAt.comp (β x) hΦ).contDiffAt.differentiableAt (by simp)
  have hd := framedDerivative_outer_comp_at (e.toFun ∘ Φ) β x he hβ
  apply ContinuousLinearMap.ext
  intro v
  change OperatorSum.operator (ν.orthonormal (Φ (β x))).val
    (framedDerivative ((e.toFun ∘ Φ) ∘ β) x) v = _
  rw [hd, OperatorSum.operator_apply]
  change _ = e.normalProductCoordinates ν Φ ⟨β x, hx⟩
    (identityBlockOperator (e.ambientDimension - 6)
      (EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
        (framedDerivative β x)) v)
  rw [identityBlockOperator_apply]
  exact (e.normalProductCoordinates_apply ν Φ ⟨β x, hx⟩
    (EuclideanSpace.finAddEquivProd v).1
    (framedDerivative β x (EuclideanSpace.finAddEquivProd v).2)).symm

theorem sphereFrameOperator_product_cancel (f : Sphere 3 → M)
    (β : Sphere 3 → Vector 3 × Vector 3) (x : Sphere 3) (hx : β x ∈ Φ.source)
    (hβ : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) β x)
    (hf : f =ᶠ[𝓝 x] Φ ∘ β) :
    (e.normalProductCoordinates ν Φ ⟨β x, hx⟩).symm.toContinuousLinearMap.comp
        (e.sphereFrameOperator ν f x) =
      identityBlockOperator (e.ambientDimension - 6)
        (EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
          (framedDerivative β x)) := by
  rw [e.sphereFrameOperator_eq_of_germ ν hf,
    e.sphereFrameOperator_product_factorization ν Φ β x hx hβ]
  apply ContinuousLinearMap.ext
  intro v
  exact (e.normalProductCoordinates ν Φ ⟨β x, hx⟩).symm_apply_apply _

theorem sphereFrameOperator_product_reduced (f : Sphere 3 → M)
    (β : Sphere 3 → Vector 3 × Vector 3) (x : Sphere 3) (hx : β x ∈ Φ.source)
    (hβ : MDifferentiableAt (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) β x)
    (hf : f =ᶠ[𝓝 x] Φ ∘ β)
    (V : Vector ((e.ambientDimension - 6) + 3) →L[ℝ]
      Vector ((e.ambientDimension - 6) + 3)) :
    lowerTangentBlock (e.ambientDimension - 6)
        (((e.normalProductCoordinates ν Φ ⟨β x, hx⟩).symm.toContinuousLinearMap.comp
          (e.sphereFrameOperator ν f x)).comp V) =
      (EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap.comp
        (framedDerivative β x)).comp (lowerTangentBlock (e.ambientDimension - 6) V) := by
  rw [e.sphereFrameOperator_product_cancel ν Φ f β x hx hβ hf,
    lowerTangentBlock_identityBlock_comp]

end EuclideanEmbedding

end NoExoticSixSphere
