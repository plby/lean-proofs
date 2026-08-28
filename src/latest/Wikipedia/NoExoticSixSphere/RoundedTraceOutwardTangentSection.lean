import Wikipedia.NoExoticSixSphere.RoundedTraceOutwardCoorientation
import Wikipedia.NoExoticSixSphere.SmoothImmersionTangentLift

/-!
# The smooth intrinsic outward section along the actual trace boundary

The ambient unit normal has a unique preimage under the trace immersion.
Those preimages form a smooth section of the genuine tangent bundle along
the boundary inclusion and are transverse to the actual boundary tangent
image. Smoothness is checked in tangent trivializations.
-/

noncomputable section

open Function Set Bundle
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def outwardTraceVector (p : Boundary A) : ℝ × Vector 6 :=
  (outwardNormal_mem_trace A p).choose

theorem traceDerivative_outwardTraceVector (p : Boundary A) :
    traceAmbientDerivative A p.val (outwardTraceVector A p) = outwardNormal A p :=
  (outwardNormal_mem_trace A p).choose_spec

theorem outwardTraceVector_unique (p : Boundary A) (v : ℝ × Vector 6)
    (hv : traceAmbientDerivative A p.val v = outwardNormal A p) :
    v = outwardTraceVector A p :=
  injective_traceAmbientDerivative A p.val (hv.trans (traceDerivative_outwardTraceVector A p).symm)

def outwardTangentSection : letI := traceChartedSpace A;
    Boundary A → TangentBundle (ProductHalfSpace.model (Vector 6)) (ambientSet A) := by
  let := traceChartedSpace A
  exact fun p ↦ TotalSpace.mk' (ℝ × Vector 6) p.val (outwardTraceVector A p)

theorem outwardTangentSection_proj (p : Boundary A) : letI := traceChartedSpace A;
    (outwardTangentSection A p).proj = p.val := rfl

theorem contMDiff_outwardTangentSection : letI := traceChartedSpace A;
    letI := trace_isManifold A;
    letI := boundaryChartedSpace A;
    ContMDiff (𝓡 6) ((ProductHalfSpace.model (Vector 6)).prod 𝓘(ℝ, ℝ × Vector 6)) ∞
      (outwardTangentSection A) := by
  let := traceChartedSpace A
  let := trace_isManifold A
  let := boundaryChartedSpace A
  exact ImmersionTangentLift.contMDiff_lift (ProductHalfSpace.model (Vector 6))
    (trace_contMDiff_ambient A) (contMDiff_boundaryInclusion A) (contMDiff_outwardNormal A)
    (injective_traceAmbientDerivative A) (outwardTraceVector A)
    (traceDerivative_outwardTraceVector A)

theorem outwardNormal_not_mem_boundaryTangent (p : Boundary A) :
    outwardNormal A p ∉ (boundaryAmbientDerivative A p).range := by
  intro hp
  have hi := Submodule.inner_right_of_mem_orthogonal hp (outwardNormal_mem_boundaryNormal A p)
  rw [real_inner_self_eq_norm_sq, norm_outwardNormal] at hi
  norm_num at hi

theorem outwardTraceVector_transverse (p : Boundary A) : letI := traceChartedSpace A;
    letI := boundaryChartedSpace A;
    outwardTraceVector A p ∉ (mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
      (Subtype.val : Boundary A → ambientSet A) p).range := by
  let := traceChartedSpace A
  let := boundaryChartedSpace A
  rintro ⟨v, hv⟩
  apply outwardNormal_not_mem_boundaryTangent A p
  refine ⟨v, ?_⟩
  have hd := congrArg (fun D : Vector 6 →L[ℝ] Vector (e.ambientDimension + 6) ↦ D v)
    (boundaryAmbientDerivative_eq A p)
  exact hd.trans ((congrArg (traceAmbientDerivative A p.val) hv).trans
    (traceDerivative_outwardTraceVector A p))

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
