import Wikipedia.HopfProblem.DegreeCollapseLowRoundedTraceBoundaryEnds
import Wikipedia.NoExoticSixSphere.NormalProjection

/-! # The smooth normal projection of the actual native boundary embedding -/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def boundaryNormalProjection (p : Boundary A) :
    Vector (e.ambientDimension + (1 + (1 + (d + 1)))) →L[ℝ]
      Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  letI := boundaryChartedSpace A
  (boundaryEuclideanEmbedding A).normalProjection p

theorem boundaryNormalProjection_eq (p : Boundary A) :
    boundaryNormalProjection A p = (boundaryAmbientDerivative A p).rangeᗮ.starProjection := rfl

theorem contMDiff_boundaryNormalProjection : letI := boundaryChartedSpace A;
    ContMDiff (𝓡 7)
      𝓘(ℝ, Vector (e.ambientDimension + (1 + (1 + (d + 1)))) →L[ℝ]
        Vector (e.ambientDimension + (1 + (1 + (d + 1))))) ∞
      (boundaryNormalProjection A) := by
  let := boundaryChartedSpace A
  let := boundary_isManifold A
  exact (boundaryEuclideanEmbedding A).contMDiff_normalProjection

theorem boundaryNormalProjection_mem (p : Boundary A)
    (v : Vector (e.ambientDimension + (1 + (1 + (d + 1))))) :
    boundaryNormalProjection A p v ∈ (boundaryAmbientDerivative A p).rangeᗮ :=
  (boundaryAmbientDerivative A p).rangeᗮ.starProjection_apply_mem v

theorem boundaryTangent_le_traceTangent (p : Boundary A) :
    (boundaryAmbientDerivative A p).range ≤ (traceAmbientDerivative A p.val).range := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  rw [boundaryAmbientDerivative_eq]
  rintro _ ⟨v, rfl⟩
  exact ⟨mfderiv (𝓡 7) (ProductHalfSpace.model (Vector 7))
    (Subtype.val : Boundary A → ambientSet A) p v, rfl⟩

theorem boundaryNormalProjection_mem_trace (p : Boundary A)
    {v : Vector (e.ambientDimension + (1 + (1 + (d + 1))))}
    (hv : v ∈ (traceAmbientDerivative A p.val).range) :
    boundaryNormalProjection A p v ∈ (traceAmbientDerivative A p.val).range := by
  rw [boundaryNormalProjection_eq, Submodule.starProjection_orthogonal_val]
  exact (traceAmbientDerivative A p.val).range.sub_mem hv
    (boundaryTangent_le_traceTangent A p
      ((boundaryAmbientDerivative A p).range.starProjection_apply_mem v))

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
