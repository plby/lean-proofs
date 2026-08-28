import Wikipedia.NoExoticSixSphere.RoundedTraceBoundaryAmbientTangent
import Wikipedia.NoExoticSixSphere.NormalProjection

/-! # The smooth normal projection of the actual native boundary embedding -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def boundaryNormalProjection (p : Boundary A) :
    Vector (e.ambientDimension + 6) →L[ℝ] Vector (e.ambientDimension + 6) :=
  letI := boundaryChartedSpace A
  (boundaryEuclideanEmbedding A).normalProjection p

theorem boundaryNormalProjection_eq (p : Boundary A) :
    boundaryNormalProjection A p = (boundaryAmbientDerivative A p).rangeᗮ.starProjection := rfl

theorem contMDiff_boundaryNormalProjection : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6)
      𝓘(ℝ, Vector (e.ambientDimension + 6) →L[ℝ] Vector (e.ambientDimension + 6)) ∞
      (boundaryNormalProjection A) := by
  let := boundaryChartedSpace A
  let := boundary_isManifold A
  exact (boundaryEuclideanEmbedding A).contMDiff_normalProjection

theorem boundaryNormalProjection_mem (p : Boundary A) (v : Vector (e.ambientDimension + 6)) :
    boundaryNormalProjection A p v ∈ (boundaryAmbientDerivative A p).rangeᗮ :=
  (boundaryAmbientDerivative A p).rangeᗮ.starProjection_apply_mem v

theorem boundaryTangent_le_traceTangent (p : Boundary A) :
    (boundaryAmbientDerivative A p).range ≤ (traceAmbientDerivative A p.val).range := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  rw [boundaryAmbientDerivative_eq]
  rintro _ ⟨v, rfl⟩
  exact ⟨mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
    (Subtype.val : Boundary A → ambientSet A) p v, rfl⟩

theorem boundaryNormalProjection_mem_trace (p : Boundary A)
    {v : Vector (e.ambientDimension + 6)} (hv : v ∈ (traceAmbientDerivative A p.val).range) :
    boundaryNormalProjection A p v ∈ (traceAmbientDerivative A p.val).range := by
  rw [boundaryNormalProjection_eq, Submodule.starProjection_orthogonal_val]
  exact (traceAmbientDerivative A p.val).range.sub_mem hv
    (boundaryTangent_le_traceTangent A p
      ((boundaryAmbientDerivative A p).range.starProjection_apply_mem v))

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
